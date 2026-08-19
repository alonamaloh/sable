//! Local toolchain and checkout diagnostics for `sable doctor`.

use crate::lean;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckStatus {
    Ok,
    Warning,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Check {
    pub status: CheckStatus,
    pub name: &'static str,
    pub detail: String,
}

#[derive(Debug, Clone)]
pub struct Report {
    pub repo_root: Option<PathBuf>,
    pub checks: Vec<Check>,
}

impl Report {
    pub fn ready(&self) -> bool {
        !self
            .checks
            .iter()
            .any(|check| check.status == CheckStatus::Error)
    }

    pub fn native_ready(&self) -> bool {
        self.ready()
            && self
                .checks
                .iter()
                .any(|check| check.name == "Clang" && check.status == CheckStatus::Ok)
    }
}

/// Inspect the checkout and the commands Sable's documented workflows use.
///
/// Verification requires Cargo (for a source checkout), Lake, and the pinned
/// Lean toolchain. Clang is optional for checking and dynamic tests, but is
/// reported because native execution and the native differential gate need it.
pub fn inspect(start: &Path) -> Report {
    let repo_root = lean::find_repo_root(start);
    let mut checks = Vec::new();

    let Some(root) = repo_root.as_deref() else {
        checks.push(Check {
            status: CheckStatus::Error,
            name: "checkout",
            detail: format!(
                "no ancestor of {} contains lean/lean-toolchain",
                start.display()
            ),
        });
        return Report { repo_root, checks };
    };

    checks.push(Check {
        status: CheckStatus::Ok,
        name: "checkout",
        detail: root.display().to_string(),
    });

    checks.push(required_command("Cargo", root, "cargo", &["--version"]));

    let lean_root = root.join("lean");
    checks.push(required_command("Lake", &lean_root, "lake", &["--version"]));
    checks.push(lean_check(&lean_root));

    let prelude = lean_root.join(".lake/build/lib/lean/Sable.olean");
    checks.push(if prelude.is_file() {
        Check {
            status: CheckStatus::Ok,
            name: "prelude",
            detail: "built (lean/.lake/build/lib/lean/Sable.olean)".into(),
        }
    } else {
        Check {
            status: CheckStatus::Warning,
            name: "prelude",
            detail: "not built; run `cd lean && lake build` before the first check".into(),
        }
    });

    let runtime = root.join("runtime/hosted/sable_rt_v1.c");
    checks.push(if runtime.is_file() {
        Check {
            status: CheckStatus::Ok,
            name: "hosted runtime",
            detail: "runtime/hosted/sable_rt_v1.c".into(),
        }
    } else {
        Check {
            status: CheckStatus::Error,
            name: "hosted runtime",
            detail: format!("missing {}", runtime.display()),
        }
    });

    checks.push(clang_check(root));

    Report { repo_root, checks }
}

fn required_command(name: &'static str, cwd: &Path, program: &str, args: &[&str]) -> Check {
    match command_version(cwd, Path::new(program), args) {
        Ok(version) => Check {
            status: CheckStatus::Ok,
            name,
            detail: version,
        },
        Err(error) => Check {
            status: CheckStatus::Error,
            name,
            detail: error,
        },
    }
}

fn lean_check(lean_root: &Path) -> Check {
    let toolchain_path = lean_root.join("lean-toolchain");
    let pin = match fs::read_to_string(&toolchain_path) {
        Ok(pin) => pin,
        Err(error) => {
            return Check {
                status: CheckStatus::Error,
                name: "Lean",
                detail: format!("cannot read {}: {error}", toolchain_path.display()),
            };
        }
    };
    let reported = command_version(lean_root, Path::new("lake"), &["env", "lean", "--version"]);
    lean_check_from_probe(pin.trim(), reported)
}

fn lean_check_from_probe(pin: &str, reported: Result<String, String>) -> Check {
    let result = (|| {
        let expected = pin
            .rsplit_once(":v")
            .map(|(_, version)| version)
            .filter(|version| !version.is_empty() && !version.chars().any(char::is_whitespace))
            .ok_or_else(|| format!("unsupported Lean toolchain pin `{pin}`"))?;
        let reported = reported?;
        let actual = reported
            .strip_prefix("Lean (version ")
            .and_then(|rest| rest.split([',', ')']).next())
            .filter(|version| !version.is_empty())
            .ok_or_else(|| {
                format!("could not parse `lake env lean --version` output: {reported}")
            })?;
        if actual != expected {
            return Err(format!(
                "pinned `{pin}` requires Lean {expected}, but `lake env lean --version` reported {actual}"
            ));
        }
        Ok(format!("{pin} (Lean {actual})"))
    })();

    match result {
        Ok(detail) => Check {
            status: CheckStatus::Ok,
            name: "Lean",
            detail,
        },
        Err(detail) => Check {
            status: CheckStatus::Error,
            name: "Lean",
            detail,
        },
    }
}

fn clang_check(cwd: &Path) -> Check {
    let configured = std::env::var_os("SABLE_CLANG").map(PathBuf::from);
    clang_check_with_probe(configured, |candidate| {
        command_version(cwd, candidate, &["--version"])
    })
}

fn clang_check_with_probe(
    configured: Option<PathBuf>,
    mut probe: impl FnMut(&Path) -> Result<String, String>,
) -> Check {
    if let Some(candidate) = configured {
        return match probe(&candidate) {
            Ok(version) => Check {
                status: CheckStatus::Ok,
                name: "Clang",
                detail: format!("SABLE_CLANG={} ({version})", candidate.display()),
            },
            Err(error) => Check {
                status: CheckStatus::Warning,
                name: "Clang",
                detail: format!(
                    "configured SABLE_CLANG={} is unusable: {error}; no fallback attempted",
                    candidate.display()
                ),
            },
        };
    }

    for candidate in [
        PathBuf::from("/opt/homebrew/opt/llvm/bin/clang"),
        PathBuf::from("clang"),
    ] {
        if let Ok(version) = probe(&candidate) {
            return Check {
                status: CheckStatus::Ok,
                name: "Clang",
                detail: format!("{} ({version})", candidate.display()),
            };
        }
    }

    Check {
        status: CheckStatus::Warning,
        name: "Clang",
        detail: "not found; optional for verification, required for native execution".into(),
    }
}

fn command_version(cwd: &Path, program: &Path, args: &[&str]) -> Result<String, String> {
    let output = Command::new(program)
        .current_dir(cwd)
        .args(args)
        .output()
        .map_err(|error| format!("cannot run `{}`: {error}", program.display()))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let detail = stderr
            .lines()
            .find(|line| !line.trim().is_empty())
            .unwrap_or("");
        return Err(if detail.is_empty() {
            format!("`{}` exited with {}", program.display(), output.status)
        } else {
            format!("`{}` failed: {detail}", program.display())
        });
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    stdout
        .lines()
        .chain(stderr.lines())
        .find(|line| !line.trim().is_empty() && !line.starts_with("warning:"))
        .map(|line| line.trim().to_owned())
        .ok_or_else(|| format!("`{}` printed no version", program.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_checkout_is_a_required_failure() {
        let report = inspect(Path::new("/path/that/is/not/a/sable/checkout"));
        assert!(!report.ready());
        assert_eq!(report.checks.len(), 1);
        assert_eq!(report.checks[0].name, "checkout");
        assert_eq!(report.checks[0].status, CheckStatus::Error);
    }

    #[test]
    fn lean_check_requires_the_exact_pinned_version() {
        let pin = "leanprover/lean4:v4.32.2";
        let exact = lean_check_from_probe(
            pin,
            Ok("Lean (version 4.32.2, test-target, test-commit, Release)".into()),
        );
        assert_eq!(exact.status, CheckStatus::Ok);
        assert_eq!(exact.detail, "leanprover/lean4:v4.32.2 (Lean 4.32.2)");

        let mismatch = lean_check_from_probe(
            pin,
            Ok("Lean (version 4.32.1, test-target, test-commit, Release)".into()),
        );
        assert_eq!(mismatch.status, CheckStatus::Error);
        assert_eq!(
            mismatch.detail,
            "pinned `leanprover/lean4:v4.32.2` requires Lean 4.32.2, but `lake env lean --version` reported 4.32.1"
        );
    }

    #[test]
    fn broken_explicit_clang_is_authoritative() {
        let configured = PathBuf::from("/configured/clang");
        let mut probed = Vec::new();
        let check = clang_check_with_probe(Some(configured.clone()), |candidate| {
            probed.push(candidate.to_path_buf());
            Err("test probe failed".into())
        });

        assert_eq!(probed, vec![configured]);
        assert_eq!(check.status, CheckStatus::Warning);
        assert!(check.detail.contains("configured SABLE_CLANG="));
        assert!(check.detail.contains("no fallback attempted"));
    }
}
