//! The corpus is the compiler's conscience (stage-1 trust, design §10.1):
//! everything in corpus/verifies/ must verify; everything in
//! corpus/must-fail/ must fail with the diagnostic named in its
//! `// expect-error:` header lines.

use sable::{Options, Outcome, check_file};
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::thread;

/// Run `work` over `items` on a small thread pool; collect the failure
/// strings. The Lean checks dominate wall clock and the files are
/// independent, so this is a near-linear speedup.
fn parallel<T: Send>(items: Vec<T>, work: impl Fn(&T) -> Vec<String> + Sync) -> Vec<String> {
    let n = std::env::var("SABLE_TEST_JOBS")
        .ok()
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|n| *n > 0)
        .unwrap_or_else(|| {
            thread::available_parallelism()
                .map(|p| p.get())
                .unwrap_or(4)
                .min(8)
        });
    let items = Mutex::new(items.into_iter());
    let failures = Mutex::new(Vec::new());
    thread::scope(|s| {
        for _ in 0..n {
            s.spawn(|| {
                loop {
                    let Some(item) = items.lock().unwrap().next() else {
                        break;
                    };
                    let fs = work(&item);
                    failures.lock().unwrap().extend(fs);
                }
            });
        }
    });
    failures.into_inner().unwrap()
}

fn corpus_dir(sub: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("corpus")
        .join(sub)
}

fn sable_files(dir: &Path) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
        .filter_map(|entry| {
            let p = entry.ok()?.path();
            (p.extension()? == "sable").then_some(p)
        })
        .collect();
    files.sort();
    files
}

fn expected_errors(path: &Path) -> Vec<String> {
    std::fs::read_to_string(path)
        .unwrap()
        .lines()
        .filter_map(|l| {
            l.trim()
                .strip_prefix("// expect-error:")
                .map(|s| s.trim().to_string())
        })
        .collect()
}

#[test]
fn corpus() {
    let opts = Options::default();
    let mut failures: Vec<String> = Vec::new();

    failures.extend(parallel(sable_files(&corpus_dir("verifies")), |path| {
        match check_file(path, &opts) {
            Outcome::Verified {
                obligations,
                warnings,
                ..
            } => {
                println!("ok: {} ({obligations} obligations)", path.display());
                // Warning-clean: an obligation that leans on an expensive
                // grind must get a discharge script, not linger near the
                // budget cliff (a toolchain bump could push it over).
                warnings
                    .iter()
                    .map(|w| format!("{} verified with a warning:\n{w}", path.display()))
                    .collect()
            }
            Outcome::Failed(diags) => vec![format!(
                "{} should verify but failed:\n{}",
                path.display(),
                diags
                    .iter()
                    .map(|f| f.rendered.as_str())
                    .collect::<Vec<_>>()
                    .join("\n")
            )],
        }
    }));

    // Module-diagnostic guards resolve their helper imports from
    // must-fail/mods (kept out of the top-level scan so the helpers
    // aren't themselves treated as cases). Client-boundary guards may
    // also import their verified subject, just like dynamic tests do.
    let must_fail_opts = Options {
        module_paths: vec![corpus_dir("must-fail").join("mods"), corpus_dir("verifies")],
        ..Options::default()
    };
    failures.extend(parallel(sable_files(&corpus_dir("must-fail")), |path| {
        let expected = expected_errors(path);
        assert!(
            !expected.is_empty(),
            "{} has no `// expect-error:` header",
            path.display()
        );
        match check_file(path, &must_fail_opts) {
            Outcome::Verified { .. } => vec![format!(
                "{} should FAIL (expected {:?}) but verified",
                path.display(),
                expected
            )],
            Outcome::Failed(diags) => {
                let mut out = Vec::new();
                for exp in &expected {
                    if !diags.iter().any(|d| d.name.contains(exp.as_str())) {
                        out.push(format!(
                            "{} failed, but no diagnostic matches `{exp}`; got: [{}]",
                            path.display(),
                            diags
                                .iter()
                                .map(|d| d.name.as_str())
                                .collect::<Vec<_>>()
                                .join(", ")
                        ));
                    }
                }
                println!("ok (fails as expected): {}", path.display());
                out
            }
        }
    }));

    // Dynamic-test corpus: corpus/tests must pass with no skipped
    // clauses (the whole contract corpus is inside the monitorable
    // fragment — a regression here means the fragment shrank). Test
    // files import their subjects from corpus/verifies (ADR 0013), so
    // a subject clause that is deliberately outside the fragment (an
    // unbounded ∃, say) is fenced by an `// expect-skip: <substr>`
    // header — every skip must match a fence, and every fence must
    // match a skip, so stale fences are failures too.
    let test_opts = Options {
        module_paths: vec![corpus_dir("verifies")],
        ..Options::default()
    };
    for path in sable_files(&corpus_dir("tests")) {
        let expected_skips: Vec<String> = std::fs::read_to_string(&path)
            .unwrap()
            .lines()
            .filter_map(|l| {
                l.trim()
                    .strip_prefix("// expect-skip:")
                    .map(|s| s.trim().to_string())
            })
            .collect();
        match sable::test_file(&path, &test_opts) {
            Err(diags) => failures.push(format!(
                "{} failed the front end:\n{}",
                path.display(),
                diags
                    .iter()
                    .map(|f| f.rendered.as_str())
                    .collect::<Vec<_>>()
                    .join("\n")
            )),
            Ok(reports) => {
                let mut matched_fences = vec![false; expected_skips.len()];
                for r in &reports {
                    if let Err(msg) = &r.outcome {
                        failures.push(format!("{} test {} failed: {msg}", path.display(), r.name));
                    }
                    for (clause, why) in &r.skipped {
                        let fence = expected_skips
                            .iter()
                            .position(|s| clause.contains(s.as_str()));
                        match fence {
                            Some(i) => matched_fences[i] = true,
                            None => failures.push(format!(
                                "{} test {} skipped a clause (fragment regression): {clause} — {why}",
                                path.display(),
                                r.name
                            )),
                        }
                    }
                }
                for (i, fence) in expected_skips.iter().enumerate() {
                    if !matched_fences[i] {
                        failures.push(format!(
                            "{} has a stale `expect-skip` fence (no clause skipped matching it): {fence}",
                            path.display()
                        ));
                    }
                }
                println!("ok (dynamic): {} ({} tests)", path.display(), reports.len());
            }
        }
    }

    // corpus/test-fails: each must produce a dynamic failure whose
    // message contains the expect-test-failure marker.
    for path in sable_files(&corpus_dir("test-fails")) {
        let expected: Vec<String> = std::fs::read_to_string(&path)
            .unwrap()
            .lines()
            .filter_map(|l| {
                l.trim()
                    .strip_prefix("// expect-test-failure:")
                    .map(|s| s.trim().to_string())
            })
            .collect();
        assert!(
            !expected.is_empty(),
            "{} has no `// expect-test-failure:` header",
            path.display()
        );
        match sable::test_file(&path, &test_opts) {
            Err(diags) => failures.push(format!(
                "{} failed the front end:\n{}",
                path.display(),
                diags
                    .iter()
                    .map(|f| f.rendered.as_str())
                    .collect::<Vec<_>>()
                    .join("\n")
            )),
            Ok(reports) => {
                let messages: Vec<&str> = reports
                    .iter()
                    .filter_map(|r| r.outcome.as_ref().err())
                    .map(|s| s.as_str())
                    .collect();
                for exp in &expected {
                    if !messages.iter().any(|m| m.contains(exp.as_str())) {
                        failures.push(format!(
                            "{} should fail dynamically with `{exp}`; got: [{}]",
                            path.display(),
                            messages.join(" | ")
                        ));
                    }
                }
                println!("ok (fails dynamically): {}", path.display());
            }
        }
    }

    assert!(
        failures.is_empty(),
        "\n== corpus failures ==\n{}",
        failures.join("\n\n")
    );
}
