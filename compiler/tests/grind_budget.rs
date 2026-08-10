//! The heartbeat budget on `sable_auto`'s grind tier, end to end:
//! exceeding the budget fails the obligation with a message naming the
//! budget; a success spending ≥ 1/5 of the budget verifies WITH a
//! warning that names the obligation and carries a minimized-proof
//! suggestion; the default budget stays silent. One test function: the
//! budget travels through the process environment (SABLE_GRIND_HEARTBEATS
//! → an emitted `set_option`), so the cases must not run concurrently.

use sable::{Options, Outcome, check_file};
use std::path::PathBuf;

/// The post is the pre's product commuted — omega is linear-only and
/// simp_all has no oriented rewrite for it, so only grind closes it.
const GRIND_ONLY: &str = "\
/// pre  a.get 0 * a.get 1 = 6
/// post result = a.get 1 * a.get 0
fn six(&[u32] a) -> u64 {
    return 6;
}
";

fn fixture() -> PathBuf {
    let dir = std::env::temp_dir().join("sable-grind-budget-test");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("grind_only.sable");
    std::fs::write(&path, GRIND_ONLY).unwrap();
    path
}

fn with_budget(kilo: Option<&str>) -> Outcome {
    unsafe {
        match kilo {
            Some(v) => std::env::set_var("SABLE_GRIND_HEARTBEATS", v),
            None => std::env::remove_var("SABLE_GRIND_HEARTBEATS"),
        }
    }
    let outcome = check_file(&fixture(), &Options::default());
    unsafe { std::env::remove_var("SABLE_GRIND_HEARTBEATS") };
    outcome
}

#[test]
fn grind_budget() {
    // Budget too small: the grind tier is killed, the obligation fails,
    // and the failure names the budget and its option.
    match with_budget(Some("1")) {
        Outcome::Failed(failures) => {
            assert!(
                failures
                    .iter()
                    .any(|f| f.rendered.contains("`grind` exceeded its heartbeat budget")),
                "expected a budget-exceeded failure, got: {:?}",
                failures.iter().map(|f| &f.name).collect::<Vec<_>>()
            );
        }
        Outcome::Verified { .. } => panic!("budget 1 should kill the grind tier"),
    }

    // Enough budget to succeed, but over the 1/5 warning threshold:
    // verified, with a warning naming the obligation and suggesting a
    // discharge script.
    match with_budget(Some("400")) {
        Outcome::Verified { warnings, .. } => {
            assert_eq!(warnings.len(), 1, "expected exactly one warning");
            let w = &warnings[0];
            assert!(
                w.contains("six.post.result_a_get_1_a_get_0"),
                "warning must name the obligation:\n{w}"
            );
            assert!(w.contains("expensive automation"), "warning text:\n{w}");
            assert!(
                w.contains("suggested: discharge six.post.result_a_get_1_a_get_0 by"),
                "warning must carry a ready-to-paste discharge suggestion:\n{w}"
            );
        }
        Outcome::Failed(failures) => panic!(
            "budget 400 should verify: {:?}",
            failures.iter().map(|f| &f.rendered).collect::<Vec<_>>()
        ),
    }

    // Default budget: silent success.
    match with_budget(None) {
        Outcome::Verified { warnings, .. } => {
            assert!(
                warnings.is_empty(),
                "default budget must not warn: {warnings:?}"
            );
        }
        Outcome::Failed(_) => panic!("default budget should verify"),
    }
}
