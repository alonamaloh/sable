//! The (type × context) support matrix.
//!
//! Sable's types are not uniformly usable in every position: a shape the
//! parser accepts as a local may be unrepresentable as an array element, and
//! a shape the checker admits as a parameter may have no field form. That
//! sparsity is a property worth measuring rather than rediscovering one
//! program at a time, so this test probes every cell of the grid with a
//! minimal program and pins the result in `docs/type-matrix.md`.
//!
//! The probe runs the Lean-free front end (parse → consts → mono → check),
//! so a cell answers "does the language admit this shape here", not "does
//! this program verify". A cell is open when at least one of its candidate
//! spellings passes; the recorded diagnostic is the one that closed the last
//! candidate tried, which is the error a reader is most likely to hit.
//!
//! A cell must be decided by the position's admissibility, never by the form
//! of the expression the probe happened to write. Types differ in how they
//! are constructed — an owned array is born from `alloc_array`, an affine
//! option from `none` or `some(alloc_array(...))`, a class from its `init` —
//! so a probe reusing one literal everywhere can report a cell closed when
//! only its initializer was refused. Each type therefore carries every
//! construction the language accepts for it, and a position that needs a
//! value tries them all. A candidate rejected for its initializer form is a
//! bug in this harness, not a closed cell: if a closing diagnostic names an
//! expression form rather than the type in the position, the missing
//! construction belongs in `values`.
//!
//! Run with `SABLE_BLESS=1` to rewrite the table after an intended change.

use std::path::{Path, PathBuf};

/// One probed type: how it is spelled, the expressions that construct a
/// value of it, and any declaration the spelling depends on. `values` ends
/// with the most ordinary construction, so a closed cell records the
/// diagnostic a reader writing the obvious program would meet.
struct Probe {
    name: &'static str,
    spelling: &'static str,
    values: &'static [&'static str],
    decls: &'static str,
}

const RECORD_DECL: &str = "\
record Pair #[layout(size := 16, align := 8)] {
    #[offset(0)] u64 left;
    #[offset(8)] u64 right;
}
";

const CLASS_DECL: &str = "\
class Box {
    u64 v;

    /// invariant v <= 100

    init make() {
        self.v = 0;
    }
}
";

const TYPES: &[Probe] = &[
    Probe {
        name: "u64",
        spelling: "u64",
        values: &["7"],
        decls: "",
    },
    Probe {
        name: "bool",
        spelling: "bool",
        values: &["true"],
        decls: "",
    },
    // Arrays are constructed either by a literal or by `alloc_array`; only
    // the latter yields the owned array that a sink taking ownership wants.
    Probe {
        name: "[u64]",
        spelling: "[u64]",
        values: &["alloc_array<u64>(2, 0)", "[1, 2]"],
        decls: "",
    },
    Probe {
        name: "[bool]",
        spelling: "[bool]",
        values: &["alloc_array<bool>(2, true)", "[true, false]"],
        decls: "",
    },
    Probe {
        name: "option<u64>",
        spelling: "option<u64>",
        values: &["none", "some(7)"],
        decls: "",
    },
    Probe {
        name: "option<bool>",
        spelling: "option<bool>",
        values: &["none", "some(true)"],
        decls: "",
    },
    Probe {
        name: "record",
        spelling: "Pair",
        values: &["Pair(1, 2)"],
        decls: RECORD_DECL,
    },
    // An affine option admits exactly `none` and a freshly allocated array.
    Probe {
        name: "option<[bool]>",
        spelling: "option<[bool]>",
        values: &["none", "some(alloc_array<bool>(2, true))"],
        decls: "",
    },
    Probe {
        name: "class",
        spelling: "Box",
        values: &["Box::make()"],
        decls: CLASS_DECL,
    },
];

/// One probed position, as a list of candidate programs. A type belongs in
/// the position when any candidate passes the front end, so neither a
/// binding form that only some types need (`var`, `mut`) nor a construction
/// that only some types accept reads as a missing cell.
type Context = (&'static str, fn(&Probe) -> Vec<String>);

/// Every (spelling, construction) pairing, as the candidate programs built
/// by `emit`. Positions that name a value must probe the whole product:
/// closing a cell takes every construction of the type failing, which is
/// what makes the closure a property of the position and not of one
/// initializer.
fn spellings_by_values(
    p: &Probe,
    spellings: &[String],
    emit: impl Fn(&str, &str) -> String,
) -> Vec<String> {
    let mut out = Vec::new();
    for spelling in spellings {
        for value in p.values {
            out.push(emit(spelling, value));
        }
    }
    out
}

const CONTEXTS: &[Context] = &[
    ("local", ctx_local),
    ("return", ctx_return),
    ("param", ctx_param),
    ("param &mut", ctx_param_mut),
    ("record field", ctx_record_field),
    ("class field", ctx_class_field),
    ("array element", ctx_array_element),
    ("option payload", ctx_option_payload),
    ("generic arg", ctx_generic_arg),
];

fn ctx_local(p: &Probe) -> Vec<String> {
    let bindings = [
        "var".to_string(),
        p.spelling.to_string(),
        format!("mut {}", p.spelling),
        "mut var".to_string(),
    ];
    spellings_by_values(p, &bindings, |binding, value| {
        format!(
            "{}\nfn probe() -> u64 {{\n    {binding} x = {value};\n    return 0;\n}}\n",
            p.decls
        )
    })
}

fn ctx_return(p: &Probe) -> Vec<String> {
    spellings_by_values(p, &[p.spelling.to_string()], |spelling, value| {
        format!(
            "{}\nfn probe() -> {spelling} {{\n    return {value};\n}}\n",
            p.decls
        )
    })
}

/// The borrow spelling comes first so the plain one is tried last: a reader
/// asking whether a type may be a parameter writes `T x` before `&T x`, and
/// the recorded diagnostic is the one the last candidate produced.
fn ctx_param(p: &Probe) -> Vec<String> {
    [format!("&{}", p.spelling), p.spelling.to_string()]
        .iter()
        .map(|param| {
            format!(
                "{}\nfn probe({param} x) -> u64 {{\n    return 0;\n}}\n",
                p.decls
            )
        })
        .collect()
}

fn ctx_param_mut(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe(&mut {} x) -> u64 {{\n    return 0;\n}}\n",
        p.decls, p.spelling
    )]
}

fn ctx_record_field(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nrecord Holder #[layout(size := 32, align := 8)] {{\n    #[offset(0)] {} f;\n}}\n\n\
         fn probe() -> u64 {{ return 0; }}\n",
        p.decls, p.spelling
    )]
}

fn ctx_class_field(p: &Probe) -> Vec<String> {
    spellings_by_values(p, &[p.spelling.to_string()], |spelling, value| {
        format!(
            "{}\nclass Holder {{\n    {spelling} f;\n\n    init make() {{\n        \
             self.f = {value};\n    }}\n}}\n\n\
             fn probe() -> u64 {{ return 0; }}\n",
            p.decls
        )
    })
}

fn ctx_array_element(p: &Probe) -> Vec<String> {
    let bindings = [
        "var".to_string(),
        format!("[{}]", p.spelling),
        format!("mut [{}]", p.spelling),
    ];
    spellings_by_values(p, &bindings, |binding, value| {
        format!(
            "{}\nfn probe() -> u64 {{\n    {binding} xs = [{value}];\n    return 0;\n}}\n",
            p.decls
        )
    })
}

fn ctx_option_payload(p: &Probe) -> Vec<String> {
    let bindings = [
        "var".to_string(),
        format!("option<{}>", p.spelling),
        format!("mut option<{}>", p.spelling),
    ];
    spellings_by_values(p, &bindings, |binding, value| {
        format!(
            "{}\nfn probe() -> u64 {{\n    {binding} o = some({value});\n    return 0;\n}}\n",
            p.decls
        )
    })
}

fn ctx_generic_arg(p: &Probe) -> Vec<String> {
    spellings_by_values(p, &[p.spelling.to_string()], |spelling, value| {
        format!(
            "{}\nfn id<T>(T x) -> T {{\n    return x;\n}}\n\n\
             fn probe() -> u64 {{\n    var y = id<{spelling}>({value});\n    return 0;\n}}\n",
            p.decls
        )
    })
}

/// `Ok` when the position admits the type; `Err` carries the diagnostic
/// name that closed it.
fn probe_cell(candidates: Vec<String>) -> Result<(), String> {
    let mut closed = "?".to_string();
    for source in candidates {
        match sable::front_diagnostics(&source).first() {
            None => return Ok(()),
            Some(d) => closed = d.name.clone(),
        }
    }
    Err(closed)
}

fn matrix_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("docs/type-matrix.md")
}

fn render(results: &[Vec<Result<(), String>>]) -> String {
    let mut out = String::new();
    out.push_str(
        "# The type × context matrix\n\n\
         Which types the language admits in which positions. Generated by \
         `compiler/tests/type_matrix.rs`;\nrewrite it with `SABLE_BLESS=1 cargo test \
         --test type_matrix`. A cell is `yes` when the\nLean-free front end accepts \
         some spelling of that type in that position, so it answers what the\nlanguage \
         admits, not what verifies.\n\n",
    );

    out.push_str("| type |");
    for (name, _) in CONTEXTS {
        out.push_str(&format!(" {name} |"));
    }
    out.push_str("\n|---|");
    out.push_str(&"---|".repeat(CONTEXTS.len()));
    out.push('\n');

    for (row, probe) in results.iter().zip(TYPES) {
        out.push_str(&format!("| `{}` |", probe.name));
        for cell in row {
            out.push_str(if cell.is_ok() { " yes |" } else { " no |" });
        }
        out.push('\n');
    }

    let total = TYPES.len() * CONTEXTS.len();
    let open = results.iter().flatten().filter(|c| c.is_ok()).count();
    out.push_str(&format!("\nOpen cells: {open}/{total}.\n"));

    out.push_str("\n## What closes each cell\n\n| type | context | diagnostic |\n|---|---|---|\n");
    for (row, probe) in results.iter().zip(TYPES) {
        for (cell, (context, _)) in row.iter().zip(CONTEXTS) {
            if let Err(name) = cell {
                out.push_str(&format!("| `{}` | {context} | `{name}` |\n", probe.name));
            }
        }
    }
    out
}

#[test]
fn type_matrix_is_pinned() {
    let results: Vec<Vec<Result<(), String>>> = TYPES
        .iter()
        .map(|probe| {
            CONTEXTS
                .iter()
                .map(|(_, build)| probe_cell(build(probe)))
                .collect()
        })
        .collect();

    let rendered = render(&results);
    let path = matrix_path();

    if std::env::var("SABLE_BLESS").is_ok() {
        std::fs::write(&path, &rendered).expect("write the matrix");
        return;
    }

    let recorded = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "cannot read {}: {e}\nrun with SABLE_BLESS=1 to create it",
            path.display()
        )
    });

    if recorded != rendered {
        panic!(
            "\n{} is stale.\n{}\n\
             Widening the language should open cells, never close them: check every line \
             above before blessing it with SABLE_BLESS=1.\n",
            path.display(),
            describe_drift(&recorded, &rendered)
        );
    }
}

/// What moved, named. The whole value of this pin is telling a later author
/// *which* cell changed, so a failure reports the moved cells rather than two
/// documents to diff by eye.
fn describe_drift(recorded: &str, rendered: &str) -> String {
    // Only the grid: its rows carry one field per context, which the
    // closing-diagnostic table below it does not.
    let cells = |table: &str| -> Vec<(String, Vec<String>)> {
        table
            .lines()
            .filter(|line| line.starts_with("| `"))
            .filter_map(|line| {
                let fields: Vec<String> = line
                    .trim()
                    .trim_matches('|')
                    .split('|')
                    .map(|f| f.trim().to_string())
                    .collect();
                (fields.len() == CONTEXTS.len() + 1)
                    .then(|| (fields[0].clone(), fields[1..].to_vec()))
            })
            .collect()
    };

    let (before, after) = (cells(recorded), cells(rendered));
    let contexts: Vec<&str> = CONTEXTS.iter().map(|(name, _)| *name).collect();
    let mut lines = Vec::new();

    for (ty, row_after) in &after {
        let Some((_, row_before)) = before.iter().find(|(name, _)| name == ty) else {
            lines.push(format!("  row {ty} is new"));
            continue;
        };
        for (i, (was, now)) in row_before
            .iter()
            .zip(row_after.iter())
            .enumerate()
            .filter(|(_, (was, now))| was != now)
        {
            let context = contexts.get(i).copied().unwrap_or("?");
            lines.push(format!("  {ty} x {context}: was {was}, now {now}"));
        }
    }
    for (ty, _) in &before {
        if !after.iter().any(|(name, _)| name == ty) {
            lines.push(format!("  row {ty} disappeared"));
        }
    }

    if lines.is_empty() {
        // Only the prose or the closing-diagnostic table moved.
        return "The grid is unchanged; a closing diagnostic was renamed or the \
                surrounding text moved."
            .to_string();
    }
    lines.join("\n")
}
