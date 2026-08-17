//! The differential-pair harness: equivalent programs must be treated
//! equivalently, and the comparison runs without Lean.
//!
//! `corpus/pairs/` holds pairs `name.a.sable` / `name.b.sable` whose first
//! line is a marker both halves must share:
//!
//!   // pair: same-lean   the two files must produce equal front-end
//!                        diagnostic-name sets and α-equivalent obligation
//!                        sets from the in-process emission path;
//!   // pair: same-run    the two files must produce equal front-end
//!                        diagnostic-name sets and identical interpreter
//!                        outcomes for every zero-argument function.
//!
//! Why this exists: treating two spellings of one program differently is
//! the shape a false-proof defect takes before Lean ever sees it — a stale
//! symbolic chain, a skipped havoc, a write-back under the wrong name all
//! surface as a divergence between rewrites long before any goal is proved.
//! A pair pins one such comparison permanently. Obligations are compared
//! α-normalized *per file*
//! (each obligation's binders renamed positionally); binders are never
//! unified across files, so a match means the two emissions agree up to
//! bound names and nothing else.
//!
//! A pair file does not have to verify: no Lean runs here, and some pairs
//! deliberately emit an unprovable obligation because the *emission* is the
//! fact under test. What a pair may never do is diverge.

use sable::{Options, load_obligations};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Marker {
    SameLean,
    SameRun,
}

fn marker_of(path: &Path, source: &str) -> Marker {
    let first = source.lines().next().unwrap_or("").trim();
    match first {
        "// pair: same-lean" => Marker::SameLean,
        "// pair: same-run" => Marker::SameRun,
        other => panic!(
            "{}: first line must be `// pair: same-lean` or `// pair: same-run`, got `{other}`",
            path.display()
        ),
    }
}

/// Rename identifier tokens through `map`, leaving field/projection names
/// (tokens immediately preceded by `.`) untouched.
fn rename_idents(text: &str, map: &HashMap<&str, String>) -> String {
    let mut out = String::with_capacity(text.len());
    let bytes = text.as_bytes();
    let mut i = 0;
    let mut prev_byte: Option<u8> = None;
    while i < bytes.len() {
        let b = bytes[i];
        if b.is_ascii_alphabetic() || b == b'_' {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            let ident = &text[start..i];
            let after_dot = prev_byte == Some(b'.');
            match (after_dot, map.get(ident)) {
                (false, Some(renamed)) => out.push_str(renamed),
                _ => out.push_str(ident),
            }
            prev_byte = Some(bytes[i - 1]);
        } else {
            let ch_len = text[i..].chars().next().map_or(1, char::len_utf8);
            out.push_str(&text[i..i + ch_len]);
            prev_byte = Some(b);
            i += ch_len;
        }
    }
    out
}

/// One obligation, α-normalized: binders renamed positionally in the
/// binder list's own order, hypothesis and goal text rewritten through
/// that map, hypothesis *names* and every span/name/description dropped.
fn normalize_obligation(ob: &sable::vcgen::Obligation) -> String {
    let mut map: HashMap<&str, String> = HashMap::new();
    for (i, (name, _)) in ob.binders.iter().enumerate() {
        map.entry(name.as_str())
            .or_insert_with(|| format!("\u{3b1}{i}"));
    }
    let binders: Vec<String> = ob
        .binders
        .iter()
        .map(|(_, ty)| rename_idents(ty, &map))
        .collect();
    let hyps: Vec<String> = ob
        .hyps
        .iter()
        .map(|(_, prop)| rename_idents(prop, &map))
        .collect();
    format!(
        "binders [{}] hyps [{}] goal {}",
        binders.join(" ; "),
        hyps.join(" ; "),
        rename_idents(&ob.goal, &map)
    )
}

/// The multiset of α-normalized obligations a file emits.
fn normalized_multiset(vc: &sable::vcgen::VcResult) -> BTreeMap<String, usize> {
    let mut set = BTreeMap::new();
    for ob in &vc.obligations {
        *set.entry(normalize_obligation(ob)).or_insert(0) += 1;
    }
    set
}

fn multiset_diff(
    a: &BTreeMap<String, usize>,
    b: &BTreeMap<String, usize>,
) -> (Vec<String>, Vec<String>) {
    let keys: BTreeSet<&String> = a.keys().chain(b.keys()).collect();
    let mut only_a = Vec::new();
    let mut only_b = Vec::new();
    for key in keys {
        let ca = a.get(key).copied().unwrap_or(0);
        let cb = b.get(key).copied().unwrap_or(0);
        if ca > cb {
            only_a.extend(std::iter::repeat_n(key.clone(), ca - cb));
        } else if cb > ca {
            only_b.extend(std::iter::repeat_n(key.clone(), cb - ca));
        }
    }
    (only_a, only_b)
}

struct Loaded {
    /// Empty when the front end (through VC generation) accepted the file.
    diag_names: BTreeSet<String>,
    rendered: Vec<String>,
    ok: Option<(
        sable::ast::Program,
        sable::modules::ModuleSet,
        sable::vcgen::VcResult,
    )>,
}

fn load(path: &Path) -> Loaded {
    match load_obligations(path, &Options::default()) {
        Ok(ok) => Loaded {
            diag_names: BTreeSet::new(),
            rendered: Vec::new(),
            ok: Some(ok),
        },
        Err(failures) => Loaded {
            diag_names: failures.iter().map(|f| f.name.clone()).collect(),
            rendered: failures.into_iter().map(|f| f.rendered).collect(),
            ok: None,
        },
    }
}

/// Canonical interpreter outcome of every zero-argument function, by name.
fn run_outcomes(
    program: &sable::ast::Program,
    mods: &sable::modules::ModuleSet,
) -> BTreeMap<String, String> {
    program
        .fns
        .iter()
        .filter(|f| f.params.is_empty())
        .map(|f| {
            let outcome = sable::interp::run_fn(program, mods, &f.name);
            (
                f.name.clone(),
                sable::svm::canonical_outcome(program, outcome),
            )
        })
        .collect()
}

fn check_pair(stem: &str, a: &Path, b: &Path, failures: &mut Vec<String>) {
    let source_a = std::fs::read_to_string(a).unwrap();
    let source_b = std::fs::read_to_string(b).unwrap();
    let marker = marker_of(a, &source_a);
    let marker_b = marker_of(b, &source_b);
    if marker != marker_b {
        failures.push(format!(
            "{stem}: the two halves carry different pair markers ({marker:?} vs {marker_b:?})"
        ));
        return;
    }

    let la = load(a);
    let lb = load(b);

    // (1) Front-end diagnostic-name sets must agree, for either marker.
    if la.diag_names != lb.diag_names {
        failures.push(format!(
            "{stem}: front-end diagnostic names diverge\n  a: {:?}\n  b: {:?}\n  a rendered:\n{}\n  b rendered:\n{}",
            la.diag_names,
            lb.diag_names,
            la.rendered.join("\n"),
            lb.rendered.join("\n"),
        ));
        return;
    }
    let (Some((prog_a, mods_a, vc_a)), Some((prog_b, mods_b, vc_b))) = (&la.ok, &lb.ok) else {
        // Both halves were refused with the same names: the pair pins the
        // refusal's breadth, and there is nothing further to compare.
        return;
    };

    match marker {
        // (2) α-normalized obligation multisets from the emission path.
        Marker::SameLean => {
            let set_a = normalized_multiset(vc_a);
            let set_b = normalized_multiset(vc_b);
            if set_a != set_b {
                let (only_a, only_b) = multiset_diff(&set_a, &set_b);
                failures.push(format!(
                    "{stem}: obligation sets diverge ({} vs {} obligations)\n  only in a ({}):\n{}\n  only in b ({}):\n{}",
                    vc_a.obligations.len(),
                    vc_b.obligations.len(),
                    only_a.len(),
                    only_a
                        .iter()
                        .map(|o| format!("    {o}"))
                        .collect::<Vec<_>>()
                        .join("\n"),
                    only_b.len(),
                    only_b
                        .iter()
                        .map(|o| format!("    {o}"))
                        .collect::<Vec<_>>()
                        .join("\n"),
                ));
            }
        }
        // (3) Interpreter outcomes for every zero-argument function.
        Marker::SameRun => {
            let runs_a = run_outcomes(prog_a, mods_a);
            let runs_b = run_outcomes(prog_b, mods_b);
            let names_a: BTreeSet<&String> = runs_a.keys().collect();
            let names_b: BTreeSet<&String> = runs_b.keys().collect();
            if names_a != names_b {
                failures.push(format!(
                    "{stem}: zero-argument entry sets diverge\n  a: {names_a:?}\n  b: {names_b:?}"
                ));
                return;
            }
            for (name, outcome_a) in &runs_a {
                let outcome_b = &runs_b[name];
                if outcome_a != outcome_b {
                    failures.push(format!(
                        "{stem}::{name}: interpreter outcomes diverge\n  a: {outcome_a}\n  b: {outcome_b}"
                    ));
                }
            }
        }
    }
}

#[test]
fn differential_pairs() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("corpus")
        .join("pairs");
    let mut halves: BTreeMap<String, (Option<PathBuf>, Option<PathBuf>)> = BTreeMap::new();
    for entry in
        std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("cannot read {}: {e}", dir.display()))
    {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|ext| ext != "sable") {
            continue;
        }
        let file = path.file_name().unwrap().to_string_lossy().into_owned();
        let (stem, slot) = if let Some(stem) = file.strip_suffix(".a.sable") {
            (stem.to_string(), 0)
        } else if let Some(stem) = file.strip_suffix(".b.sable") {
            (stem.to_string(), 1)
        } else {
            panic!(
                "{}: pair files are named <stem>.a.sable / <stem>.b.sable",
                path.display()
            );
        };
        let entry = halves.entry(stem).or_default();
        if slot == 0 {
            entry.0 = Some(path);
        } else {
            entry.1 = Some(path);
        }
    }
    assert!(!halves.is_empty(), "no pairs in {}", dir.display());

    let mut failures = Vec::new();
    for (stem, (a, b)) in &halves {
        let (Some(a), Some(b)) = (a, b) else {
            failures.push(format!("{stem}: missing one half of the pair"));
            continue;
        };
        check_pair(stem, a, b, &mut failures);
    }
    assert!(
        failures.is_empty(),
        "{} differential pair(s) diverged:\n\n{}",
        failures.len(),
        failures.join("\n\n")
    );
}
