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
//! Run with `SABLE_BLESS=1` to rewrite the table after an intended change.

use std::path::{Path, PathBuf};

/// One probed type: how it is spelled, an expression producing a value of
/// it, and any declaration the spelling depends on.
struct Probe {
    name: &'static str,
    spelling: &'static str,
    value: &'static str,
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
    Probe { name: "u64", spelling: "u64", value: "7", decls: "" },
    Probe { name: "bool", spelling: "bool", value: "true", decls: "" },
    Probe { name: "[u64]", spelling: "[u64]", value: "[1, 2]", decls: "" },
    Probe { name: "[bool]", spelling: "[bool]", value: "[true, false]", decls: "" },
    Probe { name: "option<u64>", spelling: "option<u64>", value: "some(7)", decls: "" },
    Probe { name: "option<bool>", spelling: "option<bool>", value: "some(true)", decls: "" },
    Probe { name: "record", spelling: "Pair", value: "Pair(1, 2)", decls: RECORD_DECL },
    Probe {
        name: "option<[bool]>",
        spelling: "option<[bool]>",
        value: "some(alloc_array<bool>(2, true))",
        decls: "",
    },
    Probe { name: "class", spelling: "Box", value: "Box::make()", decls: CLASS_DECL },
];

/// One probed position, as a list of candidate programs. A type belongs in
/// the position when any candidate passes the front end, so a binding form
/// that only some types need (`var`, `mut`) does not read as a missing cell.
type Context = (&'static str, fn(&Probe) -> Vec<String>);

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
    ["var".to_string(), p.spelling.to_string(), format!("mut {}", p.spelling), "mut var".to_string()]
        .iter()
        .map(|binding| {
            format!("{}\nfn probe() -> u64 {{\n    {binding} x = {};\n    return 0;\n}}\n", p.decls, p.value)
        })
        .collect()
}

fn ctx_return(p: &Probe) -> Vec<String> {
    vec![format!("{}\nfn probe() -> {} {{\n    return {};\n}}\n", p.decls, p.spelling, p.value)]
}

fn ctx_param(p: &Probe) -> Vec<String> {
    [p.spelling.to_string(), format!("&{}", p.spelling)]
        .iter()
        .map(|param| format!("{}\nfn probe({param} x) -> u64 {{\n    return 0;\n}}\n", p.decls))
        .collect()
}

fn ctx_param_mut(p: &Probe) -> Vec<String> {
    vec![format!("{}\nfn probe(&mut {} x) -> u64 {{\n    return 0;\n}}\n", p.decls, p.spelling)]
}

fn ctx_record_field(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nrecord Holder #[layout(size := 32, align := 8)] {{\n    #[offset(0)] {} f;\n}}\n\n\
         fn probe() -> u64 {{ return 0; }}\n",
        p.decls, p.spelling
    )]
}

fn ctx_class_field(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nclass Holder {{\n    {} f;\n\n    init make() {{\n        self.f = {};\n    }}\n}}\n\n\
         fn probe() -> u64 {{ return 0; }}\n",
        p.decls, p.spelling, p.value
    )]
}

fn ctx_array_element(p: &Probe) -> Vec<String> {
    ["var".to_string(), format!("[{}]", p.spelling), format!("mut [{}]", p.spelling)]
        .iter()
        .map(|binding| {
            format!("{}\nfn probe() -> u64 {{\n    {binding} xs = [{}];\n    return 0;\n}}\n", p.decls, p.value)
        })
        .collect()
}

fn ctx_option_payload(p: &Probe) -> Vec<String> {
    [
        "var".to_string(),
        format!("option<{}>", p.spelling),
        format!("mut option<{}>", p.spelling),
    ]
    .iter()
    .map(|binding| {
        format!("{}\nfn probe() -> u64 {{\n    {binding} o = some({});\n    return 0;\n}}\n", p.decls, p.value)
    })
    .collect()
}

fn ctx_generic_arg(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn id<T>(T x) -> T {{\n    return x;\n}}\n\n\
         fn probe() -> u64 {{\n    var y = id<{}>({});\n    return 0;\n}}\n",
        p.decls, p.spelling, p.value
    )]
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
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().join("docs/type-matrix.md")
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
            CONTEXTS.iter().map(|(_, build)| probe_cell(build(probe))).collect()
        })
        .collect();

    let rendered = render(&results);
    let path = matrix_path();

    if std::env::var("SABLE_BLESS").is_ok() {
        std::fs::write(&path, &rendered).expect("write the matrix");
        return;
    }

    let recorded = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!("cannot read {}: {e}\nrun with SABLE_BLESS=1 to create it", path.display())
    });

    assert_eq!(
        recorded,
        rendered,
        "\n{} is stale.\n\
         A cell changed state, or a diagnostic was renamed. Widening the language should \
         open cells, never close them: check the diff before blessing it with \
         SABLE_BLESS=1.\n",
        path.display()
    );
}
