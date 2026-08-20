use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn command_output(program: &OsStr, arguments: &[&str], directory: &Path) -> Option<String> {
    let output = Command::new(program)
        .args(arguments)
        .current_dir(directory)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let output = String::from_utf8(output.stdout).ok()?;
    let output = output.trim();
    (!output.is_empty()).then(|| output.split_whitespace().collect::<Vec<_>>().join(" "))
}

fn fnv64(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

fn git_directory(repo_root: &Path) -> Option<PathBuf> {
    let dot_git = repo_root.join(".git");
    if dot_git.is_dir() {
        return Some(dot_git);
    }
    let pointer = fs::read_to_string(dot_git).ok()?;
    let path = pointer.trim().strip_prefix("gitdir: ")?;
    let path = PathBuf::from(path);
    Some(if path.is_absolute() {
        path
    } else {
        repo_root.join(path)
    })
}

fn common_git_directory(git_dir: &Path) -> PathBuf {
    let Ok(pointer) = fs::read_to_string(git_dir.join("commondir")) else {
        return git_dir.to_owned();
    };
    let path = PathBuf::from(pointer.trim());
    if path.is_absolute() {
        path
    } else {
        git_dir.join(path)
    }
}

fn watch(path: &Path) {
    println!("cargo:rerun-if-changed={}", path.display());
}

fn watch_if_exists(path: &Path) {
    if path.exists() {
        watch(path);
    }
}

fn watch_ref_or_parent(path: &Path) {
    if path.exists() {
        watch(path);
    } else if let Some(parent) = path.parent().filter(|parent| parent.exists()) {
        // A packed ref becomes a new loose file on its next update. Watching
        // the existing parent catches that creation without watching a
        // nonexistent file (which would make Cargo rerun this script forever).
        watch(parent);
    }
}

fn watch_sources_and_git(manifest_dir: &Path, repo_root: &Path) {
    for path in [
        manifest_dir.join("build.rs"),
        manifest_dir.join("Cargo.toml"),
        manifest_dir.join("Cargo.lock"),
        manifest_dir.join("src"),
        manifest_dir.join("tests"),
    ] {
        watch(&path);
    }

    let Some(git_dir) = git_directory(repo_root) else {
        return;
    };
    let common_dir = common_git_directory(&git_dir);
    watch(&git_dir.join("HEAD"));
    watch_if_exists(&git_dir.join("packed-refs"));
    watch_if_exists(&common_dir.join("packed-refs"));
    if let Ok(head) = fs::read_to_string(git_dir.join("HEAD")) {
        if let Some(reference) = head.trim().strip_prefix("ref: ") {
            watch_ref_or_parent(&git_dir.join(reference));
            if common_dir != git_dir {
                watch_ref_or_parent(&common_dir.join(reference));
            }
        }
    }
}

fn exact_selected_profile() -> (String, String) {
    // Cargo's PROFILE variable is only a debug/release *family*: a custom
    // profile inheriting `release` also reports `release`. OUT_DIR carries the
    // selected profile's exact output-directory component. Fail closed if
    // Cargo ever changes that layout instead of silently mislabeling a timing
    // executable.
    let out_dir = PathBuf::from(
        std::env::var_os("OUT_DIR").expect("Cargo must set OUT_DIR for build scripts"),
    );
    assert_eq!(
        out_dir.file_name().and_then(|name| name.to_str()),
        Some("out")
    );
    let package_build_dir = out_dir
        .parent()
        .expect("Cargo OUT_DIR must be below a package build directory");
    let build_dir = package_build_dir
        .parent()
        .expect("Cargo package build directory must be below `build`");
    assert_eq!(
        build_dir.file_name().and_then(|name| name.to_str()),
        Some("build")
    );
    let selected_profile = build_dir
        .parent()
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
        .expect("Cargo OUT_DIR profile component must be UTF-8")
        .to_owned();
    let profile_family =
        std::env::var("PROFILE").expect("Cargo must set PROFILE for build scripts");
    (selected_profile, profile_family)
}

fn main() {
    let manifest_dir = PathBuf::from(
        std::env::var_os("CARGO_MANIFEST_DIR")
            .expect("Cargo must set CARGO_MANIFEST_DIR for build scripts"),
    );
    let repo_root = manifest_dir
        .parent()
        .expect("compiler package must live below the repository root");
    watch_sources_and_git(&manifest_dir, repo_root);

    let (selected_profile, profile_family) = exact_selected_profile();
    let revision = command_output(
        OsStr::new("git"),
        &["rev-parse", "--verify", "HEAD"],
        repo_root,
    )
    .filter(|revision| {
        matches!(revision.len(), 40 | 64) && revision.bytes().all(|byte| byte.is_ascii_hexdigit())
    })
    .unwrap_or_else(|| "unknown".to_owned());
    let git_status = Command::new("git")
        .args(["status", "--porcelain=v1", "--untracked-files=all"])
        .current_dir(repo_root)
        .output()
        .ok()
        .filter(|output| output.status.success());
    let (dirty, status_fingerprint) = match git_status {
        Some(output) => (
            if output.stdout.is_empty() {
                "false"
            } else {
                "true"
            },
            format!("fnv64:{:016x}", fnv64(&output.stdout)),
        ),
        None => ("unknown", "unknown".to_owned()),
    };
    let rustc = std::env::var_os("RUSTC")
        .and_then(|program| command_output(program.as_os_str(), &["--version"], &manifest_dir))
        .unwrap_or_else(|| "unknown".to_owned());
    let cargo = std::env::var_os("CARGO")
        .and_then(|program| command_output(program.as_os_str(), &["--version"], &manifest_dir))
        .unwrap_or_else(|| "unknown".to_owned());

    println!("cargo:rustc-env=SABLE_COMPILED_CARGO_PROFILE={selected_profile}");
    println!("cargo:rustc-env=SABLE_COMPILED_CARGO_PROFILE_FAMILY={profile_family}");
    println!("cargo:rustc-env=SABLE_COMPILED_GIT_REVISION={revision}");
    println!("cargo:rustc-env=SABLE_COMPILED_GIT_DIRTY={dirty}");
    println!("cargo:rustc-env=SABLE_COMPILED_GIT_STATUS_FINGERPRINT={status_fingerprint}");
    println!("cargo:rustc-env=SABLE_COMPILED_RUSTC_VERSION={rustc}");
    println!("cargo:rustc-env=SABLE_COMPILED_CARGO_VERSION={cargo}");
}
