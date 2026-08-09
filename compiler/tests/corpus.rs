//! The corpus is the compiler's conscience (stage-1 trust, design §10.1):
//! everything in corpus/verifies/ must verify; everything in
//! corpus/must-fail/ must fail with the diagnostic named in its
//! `// expect-error:` header lines.

use sable::{check_file, Options, Outcome};
use std::path::{Path, PathBuf};

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

    for path in sable_files(&corpus_dir("verifies")) {
        match check_file(&path, &opts) {
            Outcome::Verified { obligations, .. } => {
                println!("ok: {} ({obligations} obligations)", path.display());
            }
            Outcome::Failed(diags) => {
                failures.push(format!(
                    "{} should verify but failed:\n{}",
                    path.display(),
                    diags
                        .iter()
                        .map(|f| f.rendered.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                ));
            }
        }
    }

    for path in sable_files(&corpus_dir("must-fail")) {
        let expected = expected_errors(&path);
        assert!(
            !expected.is_empty(),
            "{} has no `// expect-error:` header",
            path.display()
        );
        match check_file(&path, &opts) {
            Outcome::Verified { .. } => {
                failures.push(format!(
                    "{} should FAIL (expected {:?}) but verified",
                    path.display(),
                    expected
                ));
            }
            Outcome::Failed(diags) => {
                for exp in &expected {
                    if !diags.iter().any(|d| d.name.contains(exp.as_str())) {
                        failures.push(format!(
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
            }
        }
    }

    assert!(
        failures.is_empty(),
        "\n== corpus failures ==\n{}",
        failures.join("\n\n")
    );
}
