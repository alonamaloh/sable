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
//! option from `none` or `some(alloc_array(...))`, a class from its `init`,
//! a raw pointer only from an unsafe exposure or another raw value — so a
//! probe reusing one literal everywhere can report a cell closed when only
//! its initializer was refused. Each type therefore carries every
//! construction the language accepts for it, and a type whose values no
//! ordinary expression can create carries a `feed` parameter that hands the
//! probe one. A candidate rejected for its initializer form is a bug in this
//! harness, not a closed cell: if a closing diagnostic names an expression
//! form rather than the type in the position, the missing construction
//! belongs in `values`.
//!
//! Each binding-mode column probes one spelling: `param` is the owned
//! spelling, and `param &` / `param &mut` are the borrow spellings, so an
//! open borrow cell says the language admits lending the type, never that
//! an owned value of it crosses the call. The `init param` / `method param`
//! pairs read the same way.
//!
//! Two coverage guards keep the grid honest as the grammar grows: every
//! spellable type shape must be probed (as a row, or as the binding-mode
//! columns for borrows) and every type position must be probed as a
//! context. A new shape or position turns them red until the matrix sees it.
//!
//! A closed cell is one of two things, and the grid says which: `not yet`
//! (work remaining) or `never` (a decision, recorded in `NEVER` with its
//! reason). The default for a closed cell is `not yet`, because claiming
//! work remains is safe where silently claiming a decision is not; `never`
//! must be written down here, cell by cell, and a `never` cell the front
//! end starts admitting is a red test in both directions.
//!
//! Run with `SABLE_BLESS=1` to rewrite the table after an intended change.

use std::path::{Path, PathBuf};

/// One probed type: how it is spelled, the expressions that construct a
/// value of it, and any declaration the spelling depends on. `values` ends
/// with the most ordinary construction, so a closed cell records the
/// diagnostic a reader writing the obvious program would meet. `feed` is a
/// parameter list added to value-consuming probe functions, for types whose
/// values only a caller can supply.
struct Probe {
    name: &'static str,
    spelling: &'static str,
    values: &'static [&'static str],
    decls: &'static str,
    feed: &'static str,
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
        feed: "",
    },
    Probe {
        name: "bool",
        spelling: "bool",
        values: &["true"],
        decls: "",
        feed: "",
    },
    // Arrays are constructed either by a literal or by `alloc_array`; only
    // the latter yields the owned array that a sink taking ownership wants.
    Probe {
        name: "[u64]",
        spelling: "[u64]",
        values: &["alloc_array<u64>(2, 0)", "[1, 2]"],
        decls: "",
        feed: "",
    },
    Probe {
        name: "[bool]",
        spelling: "[bool]",
        values: &["alloc_array<bool>(2, true)", "[true, false]"],
        decls: "",
        feed: "",
    },
    Probe {
        name: "[record]",
        spelling: "[Pair]",
        values: &[
            "alloc_array<Pair>(2, Pair(1, 2))",
            "[Pair(1, 2), Pair(3, 4)]",
        ],
        decls: RECORD_DECL,
        feed: "",
    },
    Probe {
        name: "slots<u64>",
        spelling: "slots<u64>",
        values: &["alloc_slots<u64>(2)"],
        decls: "",
        feed: "",
    },
    Probe {
        name: "option<u64>",
        spelling: "option<u64>",
        values: &["none", "some(7)"],
        decls: "",
        feed: "",
    },
    Probe {
        name: "option<bool>",
        spelling: "option<bool>",
        values: &["none", "some(true)"],
        decls: "",
        feed: "",
    },
    Probe {
        name: "record",
        spelling: "Pair",
        values: &["Pair(1, 2)"],
        decls: RECORD_DECL,
        feed: "",
    },
    // An affine option admits exactly `none` and a freshly allocated array.
    Probe {
        name: "option<[bool]>",
        spelling: "option<[bool]>",
        values: &["none", "some(alloc_array<bool>(2, true))"],
        decls: "",
        feed: "",
    },
    Probe {
        name: "class",
        spelling: "Box",
        values: &["Box::make()"],
        decls: CLASS_DECL,
        feed: "",
    },
    // A raw pointer is born inside an unsafe exposure; no ordinary
    // expression creates one, so value-consuming probes are fed one.
    Probe {
        name: "raw<u8>",
        spelling: "raw<u8>",
        values: &["src"],
        decls: "",
        feed: "raw<u8> src",
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
    ("param &", ctx_param_shared),
    ("param &mut", ctx_param_mut),
    ("record field", ctx_record_field),
    ("class field", ctx_class_field),
    ("array element", ctx_array_element),
    ("slot payload", ctx_slot_payload),
    ("option payload", ctx_option_payload),
    ("generic arg", ctx_generic_arg),
    ("for index", ctx_for_index),
    ("const", ctx_const),
    ("cast target", ctx_cast_target),
    ("trait-impl target", ctx_trait_impl_target),
    ("raw element", ctx_raw_element),
    ("resource extent", ctx_resource_extent),
    ("resource map key", ctx_resource_map_key),
    ("init param", ctx_init_param),
    ("init param &", ctx_init_param_shared),
    ("method param", ctx_method_param),
    ("method param &", ctx_method_param_shared),
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
            "{}\nfn probe({}) -> u64 {{\n    {binding} x = {value};\n    return 0;\n}}\n",
            p.decls, p.feed
        )
    })
}

fn ctx_return(p: &Probe) -> Vec<String> {
    spellings_by_values(p, &[p.spelling.to_string()], |spelling, value| {
        format!(
            "{}\nfn probe({}) -> {spelling} {{\n    return {value};\n}}\n",
            p.decls, p.feed
        )
    })
}

fn ctx_param(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe({} x) -> u64 {{\n    return 0;\n}}\n",
        p.decls, p.spelling
    )]
}

fn ctx_param_shared(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe(&{} x) -> u64 {{\n    return 0;\n}}\n",
        p.decls, p.spelling
    )]
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
            "{}\nfn probe({}) -> u64 {{\n    {binding} xs = [{value}];\n    return 0;\n}}\n",
            p.decls, p.feed
        )
    })
}

fn ctx_slot_payload(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe() -> u64 {{\n    slots<{}> xs = alloc_slots<{}>(1);\n    return 0;\n}}\n",
        p.decls, p.spelling, p.spelling
    )]
}

fn ctx_option_payload(p: &Probe) -> Vec<String> {
    let bindings = [
        "var".to_string(),
        format!("option<{}>", p.spelling),
        format!("mut option<{}>", p.spelling),
    ];
    spellings_by_values(p, &bindings, |binding, value| {
        format!(
            "{}\nfn probe({}) -> u64 {{\n    {binding} o = some({value});\n    return 0;\n}}\n",
            p.decls, p.feed
        )
    })
}

fn ctx_generic_arg(p: &Probe) -> Vec<String> {
    spellings_by_values(p, &[p.spelling.to_string()], |spelling, value| {
        format!(
            "{}\nfn id<T>(T x) -> T {{\n    return x;\n}}\n\n\
             fn probe({}) -> u64 {{\n    var y = id<{spelling}>({value});\n    return 0;\n}}\n",
            p.decls, p.feed
        )
    })
}

fn ctx_for_index(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe() -> u64 {{\n    mut u64 t = 0;\n    \
         for ({} i : range(2)) {{\n        t = t + 1;\n    }}\n    return 0;\n}}\n",
        p.decls, p.spelling
    )]
}

fn ctx_const(p: &Probe) -> Vec<String> {
    spellings_by_values(p, &[p.spelling.to_string()], |spelling, value| {
        format!(
            "{}\nconst {spelling} K = {value};\n\nfn probe() -> u64 {{\n    return 0;\n}}\n",
            p.decls
        )
    })
}

fn ctx_cast_target(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe() -> u64 {{\n    u32 a = 1;\n    var x = widen<{}>(a);\n    \
         return 0;\n}}\n",
        p.decls, p.spelling
    )]
}

fn ctx_trait_impl_target(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\ntrait Marked {{\n    fn mark(Self x) -> u64;\n}}\n\n\
         impl Marked for {spelling} {{\n    fn mark({spelling} x) -> u64 {{\n        \
         return 0;\n    }}\n}}\n\nfn probe() -> u64 {{\n    return 0;\n}}\n",
        p.decls,
        spelling = p.spelling
    )]
}

fn ctx_raw_element(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe(raw<{}> x) -> u64 {{\n    return 0;\n}}\n",
        p.decls, p.spelling
    )]
}

fn ctx_resource_extent(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe(resource &mut PointsTo<{}> c) -> u64 {{\n    return 0;\n}}\n",
        p.decls, p.spelling
    )]
}

fn ctx_resource_map_key(p: &Probe) -> Vec<String> {
    vec![format!(
        "{}\nfn probe(resource &mut ResourceMap<{}, PointsTo<u64>> m) -> u64 {{\n    \
         return 0;\n}}\n",
        p.decls, p.spelling
    )]
}

fn member_probe(decls: &str, member: &str) -> String {
    format!(
        "{decls}\nclass Holder {{\n    u64 v;\n\n    init make() {{\n        \
         self.v = 0;\n    }}\n{member}}}\n\nfn probe() -> u64 {{ return 0; }}\n"
    )
}

fn ctx_init_param(p: &Probe) -> Vec<String> {
    vec![member_probe(
        p.decls,
        &format!(
            "\n    init with({} x) {{\n        self.v = 0;\n    }}\n",
            p.spelling
        ),
    )]
}

fn ctx_init_param_shared(p: &Probe) -> Vec<String> {
    vec![member_probe(
        p.decls,
        &format!(
            "\n    init with(&{} x) {{\n        self.v = 0;\n    }}\n",
            p.spelling
        ),
    )]
}

fn ctx_method_param(p: &Probe) -> Vec<String> {
    vec![member_probe(
        p.decls,
        &format!(
            "\n    fn poke(&self, {} x) -> u64 {{\n        return 0;\n    }}\n",
            p.spelling
        ),
    )]
}

fn ctx_method_param_shared(p: &Probe) -> Vec<String> {
    vec![member_probe(
        p.decls,
        &format!(
            "\n    fn poke(&self, &{} x) -> u64 {{\n        return 0;\n    }}\n",
            p.spelling
        ),
    )]
}

/// The cells that never open, each with its reason. Everything closed and
/// not listed here reads `not yet` — the conservative default, because a
/// missing entry claims only that work remains, while a wrong entry would
/// silently close off design space. Reversing one of these decisions is
/// deleting its entry (with the reasoning that outgrew it) and blessing;
/// a listed cell the front end admits is a red test until then.
const NEVER: &[(&str, &[&str], &str)] = &[
    (
        "for index",
        &[
            "bool",
            "[u64]",
            "[bool]",
            "[record]",
            "option<u64>",
            "option<bool>",
            "record",
            "option<[bool]>",
            "class",
            "raw<u8>",
        ],
        "a range index is an integer",
    ),
    (
        "cast target",
        &[
            "bool",
            "[u64]",
            "[bool]",
            "[record]",
            "option<u64>",
            "option<bool>",
            "record",
            "option<[bool]>",
            "class",
            "raw<u8>",
        ],
        "`widen`/`narrow` convert between integer types; every other conversion is \
         spelled as the operation it is",
    ),
    (
        "param &",
        &[
            "u64",
            "bool",
            "option<u64>",
            "option<bool>",
            "record",
            "raw<u8>",
        ],
        "a shared borrow of a copyable value is indistinguishable from the value; pass \
         it by value",
    ),
    (
        "init param &",
        &[
            "u64",
            "bool",
            "option<u64>",
            "option<bool>",
            "record",
            "raw<u8>",
        ],
        "a shared borrow of a copyable value is indistinguishable from the value; pass \
         it by value",
    ),
    (
        "method param &",
        &[
            "u64",
            "bool",
            "option<u64>",
            "option<bool>",
            "record",
            "raw<u8>",
        ],
        "a shared borrow of a copyable value is indistinguishable from the value; pass \
         it by value",
    ),
    (
        "record field",
        &["[u64]", "[bool]", "[record]"],
        "a `#[layout]` record is a plain copyable value with fixed storage geometry; \
         an array owns heap storage",
    ),
    (
        "record field",
        &["option<[bool]>"],
        "record values copy freely; an affine value has exactly one owner",
    ),
    (
        "record field",
        &["class"],
        "record values copy freely; class ownership cannot be copied",
    ),
    (
        "const",
        &["option<[bool]>"],
        "a constant copies freely; an affine value has exactly one owner",
    ),
    (
        "const",
        &["class"],
        "a class value owns storage and a destructor; a constant owns nothing",
    ),
    (
        "const",
        &["raw<u8>"],
        "a raw pointer is provenance plus an offset (ADR 0025), and a constant has \
         neither",
    ),
    (
        "resource map key",
        &["[u64]", "[bool]", "[record]", "option<[bool]>", "class"],
        "a map key is a pure value compared by equality; an owning value cannot be one",
    ),
];

/// The recorded reason a cell never opens, if one is recorded.
fn never_reason(ty: &str, context: &str) -> Option<&'static str> {
    NEVER
        .iter()
        .find(|(ctx, rows, _)| *ctx == context && rows.contains(&ty))
        .map(|(_, _, reason)| *reason)
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
         admits, not what verifies.\n\nA closed cell says which kind of closed it is: \
         `not yet` is work remaining, and\n`never` is a decision — every `never` \
         carries a recorded reason (the table below),\nand a `never` cell the front \
         end starts admitting is a red test. The default for\na closed cell is \
         `not yet`, so nothing becomes a decision by omission.\n\nEach binding-mode \
         column probes one spelling: \
         `param` is the owned spelling, and\n`param &` / `param &mut` are the borrow \
         spellings, so an open borrow cell says the\nlanguage admits lending the type, \
         never that an owned value of it crosses the call.\nThe `init param` / `method \
         param` pairs read the same way.\n\n",
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
        for (cell, (context, _)) in row.iter().zip(CONTEXTS) {
            out.push_str(match cell {
                Ok(()) => " yes |",
                Err(_) if never_reason(probe.name, context).is_some() => " never |",
                Err(_) => " not yet |",
            });
        }
        out.push('\n');
    }

    let open = results.iter().flatten().filter(|c| c.is_ok()).count();
    let never: usize = results
        .iter()
        .zip(TYPES)
        .map(|(row, probe)| {
            row.iter()
                .zip(CONTEXTS)
                .filter(|(cell, (context, _))| {
                    cell.is_err() && never_reason(probe.name, context).is_some()
                })
                .count()
        })
        .sum();
    let intended = TYPES.len() * CONTEXTS.len() - never;
    out.push_str(&format!(
        "\nOpen cells: {open} of {intended} intended; {never} never open by design.\n"
    ));

    out.push_str(
        "\n## Cells that never open\n\n\
         Reversing one of these is deleting its `NEVER` entry in \
         `compiler/tests/type_matrix.rs`\n(with the reasoning that outgrew it) and \
         blessing.\n\n| context | types | reason |\n|---|---|---|\n",
    );
    for (context, rows, reason) in NEVER {
        let types = rows
            .iter()
            .map(|r| format!("`{r}`"))
            .collect::<Vec<_>>()
            .join(", ");
        out.push_str(&format!("| {context} | {types} | {reason} |\n"));
    }

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
    // The decision table names real cells, once each.
    let mut seen = std::collections::BTreeSet::new();
    for (context, rows, _) in NEVER {
        assert!(
            CONTEXTS.iter().any(|(name, _)| name == context),
            "NEVER names the context `{context}`, which does not exist"
        );
        for row in *rows {
            assert!(
                TYPES.iter().any(|probe| probe.name == *row),
                "NEVER names the row `{row}`, which does not exist"
            );
            assert!(
                seen.insert((*context, *row)),
                "NEVER lists `{row}` × `{context}` twice"
            );
        }
    }

    let results: Vec<Vec<Result<(), String>>> = TYPES
        .iter()
        .map(|probe| {
            CONTEXTS
                .iter()
                .map(|(_, build)| probe_cell(build(probe)))
                .collect()
        })
        .collect();

    // A cell recorded as never-by-design that the front end admits is a
    // contradiction the bless flag must not be able to paper over: either
    // the admission is a bug, or the decision is being reversed — and a
    // reversal starts by deleting the entry, not by blessing around it.
    for (row, probe) in results.iter().zip(TYPES) {
        for (cell, (context, _)) in row.iter().zip(CONTEXTS) {
            assert!(
                !(cell.is_ok() && never_reason(probe.name, context).is_some()),
                "`{}` × `{context}` is recorded as never opening, but the front end \
                 admits it; delete its NEVER entry (with the reasoning that outgrew \
                 it) if this is a deliberate reversal",
                probe.name
            );
        }
    }

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

/// How a spellable type shape is witnessed by the matrix.
enum ShapeWitness {
    /// Rows whose spelling has this shape.
    Rows(&'static [&'static str]),
    /// Contexts that apply this shape to every row.
    Contexts(&'static [&'static str]),
    /// Deliberately not in the grid; the reason names what watches it.
    Elsewhere(&'static str),
}

/// Every spellable type shape is probed.
///
/// The shapes come from the parser's own enumeration, so a new shape in the
/// grammar is red here until this map says how the matrix sees it — as a
/// row, as a context that wraps every row, or as a recorded decision naming
/// the measurement that watches it instead.
#[test]
fn every_spellable_type_shape_is_probed() {
    for shape in sable::parser::type_shape_names() {
        let witness = match shape {
            "Int" => ShapeWitness::Rows(&["u64"]),
            "Bool" => ShapeWitness::Rows(&["bool"]),
            "Record" => ShapeWitness::Rows(&["record"]),
            "Class" => ShapeWitness::Rows(&["class"]),
            "Array" => ShapeWitness::Rows(&["[u64]", "[bool]", "[record]"]),
            "Slots" => ShapeWitness::Rows(&["slots<u64>"]),
            "Option" => ShapeWitness::Rows(&["option<u64>", "option<bool>", "option<[bool]>"]),
            "Raw" => ShapeWitness::Rows(&["raw<u8>"]),
            // A borrow is a binding-mode wrapper (ADR 0067), so it is
            // probed as a mode of every row rather than as a row.
            "Borrow" => {
                ShapeWitness::Contexts(&["param &", "param &mut", "init param &", "method param &"])
            }
            // A type parameter is in scope only inside a template; the
            // `generic arg` context probes instantiation, and the
            // shape-admission table's `type parameter` rows watch every
            // stage gate directly.
            "Param" => ShapeWitness::Elsewhere(
                "docs/shape-admission.md rows `type parameter` and `[type parameter]`",
            ),
            // A resource value is born only from sealed operations under
            // consumption discipline, so no minimal probe program owns one;
            // the resource-prefix grammar keeps the shape out of nested
            // positions, the `resource extent` / `resource map key`
            // contexts probe its own positions, and the shape-admission
            // table's resource rows watch every stage gate directly.
            "Resource" => ShapeWitness::Elsewhere(
                "docs/shape-admission.md rows `resource`, `resource<record>`, `resource &`, \
                 `resource &mut`",
            ),
            other => panic!(
                "type shape `{other}` has no witness in the matrix: add a row for it (or a \
                 recorded decision here) so the grid measures it"
            ),
        };
        match witness {
            ShapeWitness::Rows(rows) => {
                for row in rows {
                    assert!(
                        TYPES.iter().any(|probe| probe.name == *row),
                        "shape `{shape}` names the matrix row `{row}`, which does not exist"
                    );
                }
            }
            ShapeWitness::Contexts(contexts) => {
                for context in contexts {
                    assert!(
                        CONTEXTS.iter().any(|(name, _)| name == context),
                        "shape `{shape}` names the matrix context `{context}`, which does \
                         not exist"
                    );
                }
            }
            ShapeWitness::Elsewhere(_) => {}
        }
    }
}

/// Every position a type can be written in is probed as a context.
///
/// The positions come from the parser's own enumeration, so a new `TyPos`
/// is red here until the matrix grows a context for it.
#[test]
fn every_type_position_is_probed() {
    for position in sable::parser::type_position_names() {
        let contexts: &[&str] = match position {
            "param" => &["param"],
            "borrow param" => &["param &", "param &mut"],
            "return" => &["return"],
            "local" => &["local"],
            "record field" => &["record field"],
            "class field" => &["class field"],
            "array element" => &["array element"],
            "slot payload" => &["slot payload"],
            "option payload" => &["option payload"],
            "for index" => &["for index"],
            "const" => &["const"],
            "cast target" => &["cast target"],
            "trait-impl target" => &["trait-impl target"],
            "raw element" => &["raw element"],
            "resource extent" => &["resource extent"],
            "resource map key" => &["resource map key"],
            other => panic!(
                "type position `{other}` has no matrix context: add one so the grid \
                 measures it"
            ),
        };
        for context in contexts {
            assert!(
                CONTEXTS.iter().any(|(name, _)| name == context),
                "position `{position}` names the matrix context `{context}`, which does \
                 not exist"
            );
        }
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
