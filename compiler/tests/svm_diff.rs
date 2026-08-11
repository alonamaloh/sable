//! SVM differential harness (design §10): every function in
//! corpus/svm-diff runs on both trusted executables — the tree-walking
//! interpreter (`interp.rs`) and the Lean SVM evaluator
//! (`lean/Sable/SVMEval.lean`, whose agreement with the rule system is
//! kernel-checked) — and the canonical outcomes must agree exactly.
//! A divergence is a bug in one of the two semantics we otherwise
//! trust blindly.
//!
//! The harness is strict by construction: a function that cannot be
//! lowered to the machine's core subset is a hard failure, not a skip.

use sable::{Options, load_checked};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Allocation capacity: must match the interpreter's alloc_array limit.
const CAP: u64 = 50_000_000;
/// Small-step budget for the Lean runner; diff programs are tiny.
const FUEL: u64 = 1_000_000;

fn repo_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
}

#[test]
fn svm_differential() {
    let opts = Options::default();
    let dir = repo_root().join("corpus").join("svm-diff");
    let mut files: Vec<PathBuf> = std::fs::read_dir(&dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
        .filter_map(|entry| {
            let p = entry.ok()?.path();
            (p.extension()? == "sable").then_some(p)
        })
        .collect();
    files.sort();
    assert!(!files.is_empty(), "no differential subjects in {}", dir.display());

    // Per file: the program environment (every function, callable) and
    // the zero-argument subjects that run on both sides.
    let mut progs: Vec<(usize, String)> = Vec::new();
    let mut cases: Vec<(String, usize, String, String)> = Vec::new();
    for (fi, path) in files.iter().enumerate() {
        let (program, mods) = match load_checked(path, &opts) {
            Ok(x) => x,
            Err(fs) => panic!(
                "{} failed the front end:\n{}",
                path.display(),
                fs.iter().map(|f| f.rendered.as_str()).collect::<Vec<_>>().join("\n")
            ),
        };
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        let entries: Vec<String> = program
            .fns
            .iter()
            .map(|f| {
                sable::svm::lower_fn_entry(f).unwrap_or_else(|e| {
                    panic!("{stem}::{} is not in the SVM core subset: {e}", f.name)
                })
            })
            .collect();
        progs.push((fi, entries.join(", ")));
        for f in program.fns.iter().filter(|f| f.params.is_empty()) {
            let id = format!("{stem}::{}", f.name);
            let term = sable::svm::lower_fn(f)
                .unwrap_or_else(|e| panic!("{id} is not in the SVM core subset: {e}"));
            let outcome = sable::svm::canonical_outcome(sable::interp::run_fn(
                &program, &mods, &f.name,
            ));
            cases.push((id, fi, term, outcome));
        }
    }

    // One generated driver, one Lean invocation for the whole corpus.
    let mut driver = String::from("import Sable.SVMEval\nopen Sable.SVM\n");
    for (fi, entries) in &progs {
        driver.push_str(&format!("def prog{fi} : Prog := Prog.ofList [{entries}]\n"));
    }
    for (i, (id, fi, term, _)) in cases.iter().enumerate() {
        driver.push_str(&format!("def p{i} : List Stmt := {term}\n"));
        driver.push_str(&format!(
            "#eval IO.println (\"{id}\\t\" ++ (run prog{fi} {CAP} {FUEL} (.run p{i} Env.empty [] .empty)).render)\n"
        ));
    }
    let driver_path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("svm_diff_driver.lean");
    std::fs::write(&driver_path, &driver).unwrap();

    let lean_dir = repo_root().join("lean");
    let build = Command::new("lake")
        .arg("build")
        .current_dir(&lean_dir)
        .output()
        .expect("failed to run `lake build`");
    assert!(
        build.status.success(),
        "`lake build` failed:\n{}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let out = Command::new("lake")
        .args(["env", "lean"])
        .arg(&driver_path)
        .current_dir(&lean_dir)
        .output()
        .expect("failed to run `lake env lean`");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        out.status.success(),
        "the Lean driver failed (lowering bug?):\n{stdout}{}",
        String::from_utf8_lossy(&out.stderr)
    );

    let lean_outcomes: HashMap<&str, &str> =
        stdout.lines().filter_map(|l| l.split_once('\t')).collect();
    let mut failures = Vec::new();
    for (id, _, _, interp_outcome) in &cases {
        match lean_outcomes.get(id.as_str()) {
            None => failures.push(format!("{id}: the Lean driver produced no outcome")),
            Some(lean_outcome) if lean_outcome != interp_outcome => failures.push(format!(
                "{id} DIVERGES: interp says `{interp_outcome}`, SVM says `{lean_outcome}`"
            )),
            Some(_) => println!("ok (svm-diff): {id}"),
        }
    }
    assert!(
        failures.is_empty(),
        "\n== SVM differential failures ==\n{}",
        failures.join("\n")
    );
    println!("svm-diff: {} subjects agree", cases.len());
}
