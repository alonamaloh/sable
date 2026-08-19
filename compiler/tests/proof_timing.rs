//! Release-only proof-time measurement.
//!
//! Wall time is too noisy for a per-PR gate, but a serialized, identified
//! series is useful evidence about whether the proof portfolio is scaling.
//! Run this ignored test on a stable machine with an explicit cache mode:
//!
//! ```text
//! SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1 \
//! SABLE_PROOF_TIMING_CACHE_MODE=cold-roots \
//! SABLE_PROOF_TIMING_MACHINE=ci-mac-mini-m4 \
//! cargo test --locked --test proof_timing -- --ignored --nocapture --test-threads=1
//! ```
//!
//! `cold-roots` and `warm-artifacts` are labels, not actions. The runner never
//! deletes proof artifacts; whoever records a release series must prepare the
//! stated cache condition before invoking it.

use sable::{Options, Outcome, check_file};
use serde_json::json;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("compiler crate lives below the repository root")
        .to_path_buf()
}

fn verifying_subjects() -> Vec<PathBuf> {
    let directory = repo_root().join("corpus/verifies");
    let mut paths = fs::read_dir(&directory)
        .unwrap_or_else(|error| panic!("cannot read {}: {error}", directory.display()))
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            (path.extension()?.to_str()? == "sable").then_some(path)
        })
        .collect::<Vec<_>>();
    paths.sort();
    paths
}

fn require_serial_environment(name: &str) {
    assert_eq!(
        std::env::var(name).as_deref(),
        Ok("1"),
        "release proof timing requires {name}=1"
    );
}

fn command_output(program: &str, arguments: &[&str]) -> String {
    command_output_in(None, program, arguments)
}

fn command_output_in(directory: Option<&Path>, program: &str, arguments: &[&str]) -> String {
    let mut command = Command::new(program);
    command.args(arguments);
    if let Some(directory) = directory {
        command.current_dir(directory);
    }
    command
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_owned())
        .filter(|output| !output.is_empty())
        .unwrap_or_else(|| "unavailable".into())
}

fn repository_is_dirty(root: &Path) -> bool {
    Command::new("git")
        .args([
            "-C",
            root.to_str().expect("UTF-8 repository path"),
            "status",
            "--porcelain",
        ])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .is_none_or(|output| !output.stdout.is_empty())
}

fn percentile(sorted: &[u64], numerator: usize, denominator: usize) -> u64 {
    assert!(!sorted.is_empty());
    assert!(numerator > 0 && numerator <= denominator);
    let rank = (sorted.len() * numerator).div_ceil(denominator);
    sorted[rank.saturating_sub(1)]
}

#[test]
#[ignore = "release instrumentation; wall time is not a deterministic PR gate"]
fn record_verifying_corpus_proof_times() {
    require_serial_environment("SABLE_TEST_JOBS");
    require_serial_environment("SABLE_LEAN_JOBS");
    let cache_mode = std::env::var("SABLE_PROOF_TIMING_CACHE_MODE").expect(
        "set SABLE_PROOF_TIMING_CACHE_MODE to an honest prepared state, such as cold-roots or warm-artifacts",
    );
    assert!(
        matches!(cache_mode.as_str(), "cold-roots" | "warm-artifacts"),
        "unknown proof timing cache mode `{cache_mode}`"
    );
    let machine = std::env::var("SABLE_PROOF_TIMING_MACHINE")
        .expect("set SABLE_PROOF_TIMING_MACHINE to a stable machine identity");
    let root = repo_root();
    let git_dirty = repository_is_dirty(&root);
    assert!(
        !git_dirty || std::env::var("SABLE_PROOF_TIMING_ALLOW_DIRTY").as_deref() == Ok("1"),
        "release proof timing refuses a dirty worktree; set SABLE_PROOF_TIMING_ALLOW_DIRTY=1 only for an explicitly non-release experiment"
    );
    let output_path = std::env::var_os("SABLE_PROOF_TIMING_OUT")
        .map(PathBuf::from)
        .unwrap_or_else(|| root.join("compiler/target/proof-timing.json"));

    let options = Options::default();
    let mut records = Vec::new();
    let mut failures = Vec::new();
    let started_all = Instant::now();
    for path in verifying_subjects() {
        let started = Instant::now();
        let outcome = check_file(&path, &options);
        let elapsed_ms = u64::try_from(started.elapsed().as_millis())
            .expect("one subject's proof time fits u64 milliseconds");
        let relative = path
            .strip_prefix(&root)
            .expect("corpus subject is below the repository root")
            .to_string_lossy()
            .replace('\\', "/");
        match outcome {
            Outcome::Verified {
                functions,
                obligations,
                unsafe_regions,
                deferred,
                assumed,
                warnings,
                ..
            } => {
                if !warnings.is_empty() || !deferred.is_empty() || !assumed.is_empty() {
                    failures.push(format!(
                        "{relative}: {} warning(s), {} deferred, {} assumed",
                        warnings.len(),
                        deferred.len(),
                        assumed.len()
                    ));
                }
                records.push(json!({
                    "path": relative,
                    "elapsed_ms": elapsed_ms,
                    "functions": functions,
                    "obligations": obligations,
                    "unsafe_regions": unsafe_regions,
                    "warnings": warnings.len(),
                    "deferred": deferred.len(),
                    "assumed": assumed.len(),
                }));
            }
            Outcome::Failed(diagnostics) => {
                failures.push(format!(
                    "{relative}: {}",
                    diagnostics
                        .iter()
                        .map(|diagnostic| diagnostic.name.as_str())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
                records.push(json!({
                    "path": relative,
                    "elapsed_ms": elapsed_ms,
                    "failed": true,
                    "diagnostics": diagnostics
                        .iter()
                        .map(|diagnostic| diagnostic.name.as_str())
                        .collect::<Vec<_>>(),
                }));
            }
        }
    }

    let mut durations = records
        .iter()
        .filter_map(|record| record.get("elapsed_ms")?.as_u64())
        .collect::<Vec<_>>();
    durations.sort_unstable();
    let total_ms = u64::try_from(started_all.elapsed().as_millis())
        .expect("full proof timing run fits u64 milliseconds");
    let git_commit = command_output(
        "git",
        &[
            "-C",
            root.to_str().expect("UTF-8 repository path"),
            "rev-parse",
            "HEAD",
        ],
    );
    let report = json!({
        "schema": "sable-proof-timing-v1",
        "recorded_unix_seconds": SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time is after the Unix epoch")
            .as_secs(),
        "git_commit": git_commit,
        "git_dirty": git_dirty,
        "machine": machine,
        "host": command_output("hostname", &[]),
        "os": std::env::consts::OS,
        "architecture": std::env::consts::ARCH,
        "parallelism": std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1),
        "rustc": command_output("rustc", &["--version"]),
        "lean": command_output_in(Some(&root.join("lean")), "lake", &["env", "lean", "--version"]),
        "cache_mode": cache_mode,
        "sable_test_jobs": 1,
        "sable_lean_jobs": 1,
        "summary": {
            "subjects": records.len(),
            "total_ms": total_ms,
            "sum_subject_ms": durations.iter().sum::<u64>(),
            "median_ms": percentile(&durations, 50, 100),
            "p95_ms": percentile(&durations, 95, 100),
            "max_ms": durations.last().copied().unwrap_or(0),
            "failures": failures.len(),
        },
        "subjects": records,
    });
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)
            .unwrap_or_else(|error| panic!("cannot create {}: {error}", parent.display()));
    }
    fs::write(
        &output_path,
        serde_json::to_vec_pretty(&report).expect("proof timing report is serializable"),
    )
    .unwrap_or_else(|error| panic!("cannot write {}: {error}", output_path.display()));
    println!(
        "proof timing: {} subjects, total {} ms, median {} ms, p95 {} ms, max {} ms -> {}",
        durations.len(),
        total_ms,
        percentile(&durations, 50, 100),
        percentile(&durations, 95, 100),
        durations.last().copied().unwrap_or(0),
        output_path.display()
    );
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
