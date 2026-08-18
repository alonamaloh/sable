//! The tutorial is executable documentation, on the same terms as the
//! corpus: every ```sable block in `docs/TUTORIAL.md` is compiled and
//! proved, so a language change that makes the tutorial wrong is a red
//! test rather than a page nobody re-read.
//!
//! A block follows the corpus conventions it is teaching:
//!
//!   - by default it must verify;
//!   - `// expect-error: <name>` as a line in the block means it must fail
//!     with that diagnostic (the tutorial shows several deliberate errors);
//!   - a block whose first line is `// <name>.sable` is a named file in a
//!     multi-file example: consecutive named blocks share a directory, and
//!     each is checked in turn with the others on the module path;
//!   - a block named `test_*.sable` is *run* by the dynamic checker rather
//!     than verified, because that is what the page claims it does.
//!
//! Blocks are written to a temp directory rather than the repo, so the
//! tutorial stays the only copy of its own examples.

use sable::{Options, Outcome, check_file, test_file};
use std::path::{Path, PathBuf};

/// One fenced block: its source, the diagnostics it expects, and the file
/// name a multi-file example gave it.
struct Block {
    line: usize,
    source: String,
    expected_errors: Vec<String>,
    name: Option<String>,
}

fn tutorial_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("the crate sits inside the repository")
        .join("docs")
        .join("TUTORIAL.md")
}

fn blocks(markdown: &str) -> Vec<Block> {
    let mut out = Vec::new();
    let mut lines = markdown.lines().enumerate();
    while let Some((index, line)) = lines.next() {
        if line.trim() != "```sable" {
            continue;
        }
        let mut source = String::new();
        for (_, body) in lines.by_ref() {
            if body.trim() == "```" {
                break;
            }
            source.push_str(body);
            source.push('\n');
        }
        let expected_errors = source
            .lines()
            .filter_map(|l| {
                l.trim()
                    .strip_prefix("// expect-error:")
                    .map(|s| s.trim().to_string())
            })
            .collect();
        // `// name.sable` on the first line marks a member of a multi-file
        // example; a trailing comment after it is prose for the reader.
        let name = source
            .lines()
            .next()
            .and_then(|l| l.trim().strip_prefix("// "))
            .and_then(|l| l.split_whitespace().next())
            .filter(|l| l.ends_with(".sable"))
            .map(|l| l.to_string());
        out.push(Block {
            line: index + 1,
            source,
            expected_errors,
            name,
        });
    }
    out
}

/// Consecutive named blocks form one multi-file example; every other block
/// stands alone. Returns groups whose last member is the entry point.
fn group(blocks: Vec<Block>) -> Vec<Vec<Block>> {
    let mut groups: Vec<Vec<Block>> = Vec::new();
    for block in blocks {
        match groups.last_mut() {
            Some(last) if block.name.is_some() && last.last().is_some_and(|b| b.name.is_some()) => {
                last.push(block)
            }
            _ => groups.push(vec![block]),
        }
    }
    groups
}

fn check_group(group: &[Block], dir: &Path) -> Vec<String> {
    // Every member is written first: a file that imports a sibling needs the
    // sibling on disk before any of them is checked.
    let paths: Vec<PathBuf> = group
        .iter()
        .map(|block| match &block.name {
            Some(name) => dir.join(name),
            None => dir.join("tutorial.sable"),
        })
        .collect();
    for (block, path) in group.iter().zip(&paths) {
        std::fs::write(path, &block.source).expect("write the block");
    }
    let opts = Options {
        module_paths: vec![dir.to_path_buf()],
        ..Options::default()
    };
    group
        .iter()
        .zip(&paths)
        .flat_map(|(block, path)| check_one(block, path, &opts))
        .collect()
}

/// A dynamic-test block is run rather than verified: `test_*` functions are
/// never verified, so checking one would prove nothing about the claim the
/// page makes for it.
fn run_one(block: &Block, path: &Path, opts: &Options, where_: &str) -> Vec<String> {
    match test_file(path, opts) {
        Err(failures) => vec![format!(
            "{where_} should run but failed to load:\n{}",
            failures
                .iter()
                .map(|f| f.rendered.as_str())
                .collect::<Vec<_>>()
                .join("\n")
        )],
        Ok(reports) => {
            let mut out: Vec<String> = reports
                .iter()
                .filter_map(|r| {
                    r.outcome
                        .as_ref()
                        .err()
                        .map(|e| format!("{where_}: test `{}` failed: {e}", r.name))
                })
                .collect();
            for report in &reports {
                for (clause, reason) in &report.skipped {
                    out.push(format!(
                        "{where_}: test `{}` skipped a clause (`{clause}`: {reason})",
                        report.name
                    ));
                }
            }
            if reports.is_empty() {
                out.push(format!("{where_} names no `test_*` function"));
            }
            if out.is_empty() {
                println!("ok (runs): {where_} ({} tests)", reports.len());
            }
            out
        }
    }
}

fn check_one(block: &Block, path: &Path, opts: &Options) -> Vec<String> {
    let where_ = format!("docs/TUTORIAL.md:{}", block.line);
    let is_dynamic = block
        .name
        .as_deref()
        .is_some_and(|n| n.starts_with("test_"));
    if is_dynamic {
        return run_one(block, path, opts, &where_);
    }
    match check_file(path, opts) {
        Outcome::Verified { obligations, .. } => {
            if block.expected_errors.is_empty() {
                println!("ok: {where_} ({obligations} obligations)");
                Vec::new()
            } else {
                vec![format!(
                    "{where_} should FAIL (expected {:?}) but verified",
                    block.expected_errors
                )]
            }
        }
        Outcome::Failed(diags) => {
            if block.expected_errors.is_empty() {
                return vec![format!(
                    "{where_} should verify but failed:\n{}",
                    diags
                        .iter()
                        .map(|d| d.rendered.as_str())
                        .collect::<Vec<_>>()
                        .join("\n")
                )];
            }
            let mut out = Vec::new();
            for expected in &block.expected_errors {
                if !diags.iter().any(|d| d.name.contains(expected.as_str())) {
                    out.push(format!(
                        "{where_} failed, but no diagnostic matches `{expected}`; got: [{}]",
                        diags
                            .iter()
                            .map(|d| d.name.as_str())
                            .collect::<Vec<_>>()
                            .join(", ")
                    ));
                }
            }
            if out.is_empty() {
                println!("ok (fails as expected): {where_}");
            }
            out
        }
    }
}

#[test]
fn tutorial_examples_still_compile() {
    let markdown = std::fs::read_to_string(tutorial_path()).expect("read the tutorial");
    let groups = group(blocks(&markdown));
    assert!(
        groups.len() >= 10,
        "the tutorial should carry its examples as ```sable blocks; found {}",
        groups.len()
    );

    let root = std::env::temp_dir().join(format!("sable-docs-{}", std::process::id()));
    let mut failures = Vec::new();
    for (index, group) in groups.iter().enumerate() {
        let dir = root.join(index.to_string());
        std::fs::create_dir_all(&dir).expect("create the example directory");
        failures.extend(check_group(group, &dir));
    }
    let _ = std::fs::remove_dir_all(&root);

    assert!(
        failures.is_empty(),
        "the tutorial is out of date:\n{}",
        failures.join("\n\n")
    );
}
