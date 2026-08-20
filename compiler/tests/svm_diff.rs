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
use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Allocation capacity: must match the interpreter's alloc_array limit.
const CAP: u64 = 50_000_000;
/// Small-step budget for the Lean runner; diff programs are tiny.
const FUEL: u64 = 1_000_000;

fn repo_root() -> &'static Path {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap()
}

fn bounded_lake_command(lean_dir: &Path) -> Command {
    let mut command = Command::new("lake");
    command
        .env("LEAN_NUM_THREADS", "0")
        .env("LEAN_IMPORT_WORKERS", "1")
        .current_dir(lean_dir);
    command
}

fn prelude_build_command(lean_dir: &Path) -> Command {
    let mut command = bounded_lake_command(lean_dir);
    command.args(["--quiet", "build", "Sable"]);
    command
}

fn svm_driver_command(lean_dir: &Path, driver_path: &Path) -> Command {
    let mut command = bounded_lake_command(lean_dir);
    command.args(["env", "lean"]).arg(driver_path);
    command
}

fn assert_bounded_lake_command(command: &Command, lean_dir: &Path) {
    assert_eq!(command.get_program(), OsStr::new("lake"));
    assert_eq!(command.get_current_dir(), Some(lean_dir));
    let envs = command.get_envs().collect::<Vec<_>>();
    assert!(envs.contains(&(OsStr::new("LEAN_NUM_THREADS"), Some(OsStr::new("0")))));
    assert!(envs.contains(&(OsStr::new("LEAN_IMPORT_WORKERS"), Some(OsStr::new("1")))));
}

#[test]
fn svm_lake_commands_pin_the_audited_scheduler_and_exact_target() {
    let lean_dir = Path::new("proof-environment/lean");
    let build = prelude_build_command(lean_dir);
    assert_bounded_lake_command(&build, lean_dir);
    assert_eq!(
        build.get_args().collect::<Vec<_>>(),
        ["--quiet", "build", "Sable"]
            .iter()
            .map(OsStr::new)
            .collect::<Vec<_>>()
    );

    let driver_path = Path::new("generated/svm_driver.lean");
    let driver = svm_driver_command(lean_dir, driver_path);
    assert_bounded_lake_command(&driver, lean_dir);
    assert_eq!(
        driver.get_args().collect::<Vec<_>>(),
        [
            OsStr::new("env"),
            OsStr::new("lean"),
            driver_path.as_os_str()
        ]
    );
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
    assert!(
        !files.is_empty(),
        "no differential subjects in {}",
        dir.display()
    );

    // Per file: the program environment (every function, callable) and
    // the zero-argument subjects that run on both sides.
    let mut progs: Vec<(usize, String)> = Vec::new();
    let mut cases: Vec<(String, usize, String, String)> = Vec::new();
    for (fi, path) in files.iter().enumerate() {
        let (checked, mods) = match load_checked(path, &opts) {
            Ok(x) => x,
            Err(fs) => panic!(
                "{} failed the front end:\n{}",
                path.display(),
                fs.iter()
                    .map(|f| f.rendered.as_str())
                    .collect::<Vec<_>>()
                    .join("\n")
            ),
        };
        let program = checked.program();
        let stem = path.file_stem().unwrap().to_string_lossy().into_owned();
        let entries: Vec<String> = program
            .fns
            .iter()
            .map(|f| {
                sable::svm::lower_checked_fn_entry(&checked, &f.name).unwrap_or_else(|e| {
                    panic!("{stem}::{} is not in the SVM core subset: {e}", f.name)
                })
            })
            .collect();
        progs.push((fi, entries.join(", ")));
        for f in program.fns.iter().filter(|f| f.params.is_empty()) {
            let id = format!("{stem}::{}", f.name);
            let term = sable::svm::lower_checked_fn(&checked, &f.name)
                .unwrap_or_else(|e| panic!("{id} is not in the SVM core subset: {e}"));
            let outcome = sable::svm::canonical_observed(
                &program,
                sable::interp::run_checked_fn_observed(&checked, &mods, &f.name),
            );
            cases.push((id, fi, term, outcome));
        }
    }

    // One generated driver, one Lean invocation for the whole corpus.
    let mut driver = String::from("import Sable.SVMUart\nopen Sable.SVM\n");
    for (fi, entries) in &progs {
        driver.push_str(&format!("def prog{fi} : Prog := Prog.ofList [{entries}]\n"));
    }
    for (i, (id, fi, term, _)) in cases.iter().enumerate() {
        driver.push_str(&format!("def p{i} : List Stmt := {term}\n"));
        driver.push_str(&format!(
            "#eval IO.println (\"{id}\\t\" ++ (Sable.SVMUart.run prog{fi} {CAP} {FUEL} (Sable.SVMUart.Config.bare (.run p{i} Env.empty [] .empty))).render)\n"
        ));
    }
    let driver_path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("svm_diff_driver.lean");
    std::fs::write(&driver_path, &driver).unwrap();

    let lean_dir = repo_root().join("lean");
    let build = prelude_build_command(&lean_dir)
        .output()
        .expect("failed to run `lake build`");
    assert!(
        build.status.success(),
        "`lake build` failed:\n{}{}",
        String::from_utf8_lossy(&build.stdout),
        String::from_utf8_lossy(&build.stderr)
    );
    let out = svm_driver_command(&lean_dir, &driver_path)
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

fn checked_subject(file: &str) -> sable::CheckedProgram {
    let path = repo_root().join("corpus").join("svm-diff").join(file);
    match load_checked(&path, &Options::default()) {
        Ok((checked, _)) => checked,
        Err(failures) => panic!(
            "{} failed the front end:\n{}",
            path.display(),
            failures
                .iter()
                .map(|failure| failure.rendered.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        ),
    }
}

fn position(term: &str, needle: &str) -> usize {
    term.find(needle)
        .unwrap_or_else(|| panic!("lowered term has no `{needle}`:\n{term}"))
}

#[test]
fn checked_control_routes_are_explicit_and_deterministic() {
    let checked = checked_subject("control_cleanup.sable");

    let early = sable::svm::lower_checked_fn_entry(&checked, "early_set")
        .expect("checked bare return lowers through retUnit");
    let save = position(&early, "(.scopeExit [");
    let ret = position(&early, "(.retUnit)");
    assert!(save < ret, "lexical cleanup must precede the early return");
    assert!(
        early[save..ret].contains("\"scratch\""),
        "the early-return route must clear its branch owner"
    );
    assert!(
        !early[..ret].contains("scopeExit [\"values\"]"),
        "the borrowed parameter must survive until retUnit restores its loan"
    );

    let branch = sable::svm::lower_checked_fn(&checked, "branch_fallthrough_closes_its_local")
        .expect("checked branch lowers");
    assert!(branch.contains("(.scopeExit [\"branch_local\"])"));

    let loop_term = sable::svm::lower_checked_fn(&checked, "loop_backedge_closes_its_local")
        .expect("checked loop lowers");
    let loop_body = position(&loop_term, "(.while");
    let loop_close = position(&loop_term, "(.scopeExit [\"loop_local\"])");
    assert!(loop_body < loop_close, "loop local closes on the backedge");

    let trapping =
        sable::svm::lower_checked_fn(&checked, "trapping_return_evaluates_before_cleanup")
            .expect("checked trapping expression lowers");
    let load = position(&trapping, "(.index \"values\"");
    let cleanup = position(&trapping, "(.scopeExit [");
    assert!(
        load < cleanup,
        "a trapping result is evaluated before cleanup"
    );

    let exposure = checked_subject("typed_cell_round_trip.sable");
    let first = sable::svm::lower_checked_fn(&exposure, "subj").expect("checked exposure lowers");
    let second = sable::svm::lower_checked_fn(&exposure, "subj")
        .expect("repeated checked exposure lowering succeeds");
    assert_eq!(
        first, second,
        "compiler temporary identities must be stable"
    );
    let free = first
        .rfind("(.rawFree")
        .expect("exposure epilogue releases its raw loan");
    let before_free = &first[..free];
    let after_free = &first[free..];
    assert!(
        before_free.contains("(.scopeExit ["),
        "the exposure body closes before copyback/release"
    );
    assert!(
        after_free.contains("$sable$exposure_"),
        "compiler exposure scratch closes after release"
    );
}
