# ADR 0013 — Modules v1: file-based `use` imports

Date: 2026-08-10. Status: accepted, implemented (slice 1). Separate
verification (Lean-level imports) and visibility control deliberately
deferred — see Consequences.

## Context

Every corpus test file carried a full copy of its subject — the bignum
test opened with 700 lines of `Nat` before the first `test_` function.
Copies drift, and a language whose contracts are the interface has no
excuse: a caller needs a function's *contract*, not its body. Alvaro
asked for something Rust-familiar.

## Decision

**A module is a file**; its name is the file stem. No module
declarations, no paths-in-source, no visibility control (v1 exports
everything).

```sable
use bignum;               // import everything bignum declares
use lib_pair::{bump};     // import with a checked name list
```

- **Resolution**: `use m;` finds `m.sable` in the importing file's own
  directory first, then the `-M`/`--module-path` directories in order.
  Imports are transitive and form a DAG (`module.cycle` on
  back-edges, checked before the seen-set dedup so cycles are caught,
  not silently absorbed).
- **`use m::{a, b};`** validates that each listed name exists in `m`
  (`module.unknown_name`). In v1 the list is documentation plus that
  check — it does not yet restrict the namespace (everything links
  regardless). Restriction arrives with visibility control.
- **Linking is source-level**: the loader concatenates the module
  sources (dependencies first, root at base 0) and parses each module
  in place within the combined coordinate space, so the merged AST is
  *one* Program and every downstream stage — mono, check, vcgen,
  emitter, interpreter, monitor — is unchanged and module-oblivious.
  Imported class names seed the parser's class index before a dependent
  module parses (`extern_classes`), and the flat merge reproduces that
  index order exactly.
- **Diagnostics stay per-file**: `ModuleSet.locate` maps any
  combined-source span back to `(file, line, col)`, so an error in an
  imported module renders against *that* file (`mathlib.sable:3:12`)
  even when the check was started from the importer, and cross-module
  context entries carry a `(file:line)` provenance. The LSP reports
  only the root module's diagnostics (the open file owns its errors;
  imported modules get theirs when opened).
- **Top-level name collisions across modules** are errors
  (`module.name_collision`) — no shadowing, no namespacing in v1.
  Duplicate imports are deduplicated by canonical path (the diamond
  `a → b, c; b, c → d` loads `d` once).
- **Verification is whole-DAG**: checking a root re-verifies its
  imports in the same Lean file. Correct, cache-friendly at current
  corpus scale (the daemon's warm checker amortizes the prelude), and
  honest — nothing is assumed unverified.
- `sable test` links the same way; trap and monitor reports locate
  through the module set.

## Consequences

- The dynamic-test corpus imports its subjects from `corpus/verifies`
  (`sable test -M corpus/verifies corpus/tests/…`); the bignum test is
  now `use bignum;` plus fourteen test functions. A test file may
  extend an imported trait with its own `impl` (test_hashmap adds
  `impl Hashable for u64`) — combined-source linking makes this free.
- Imports carry the subject's *full* contract — a test file can no
  longer quietly drop an unmonitorable clause the way the old copies
  did (the utf8 copy had deleted the decoder's ∃-completeness post).
  The corpus grew an explicit fence for exactly this:
  `// expect-skip: <substr>` in a test file allowlists a known
  skip, and a fence matching no actual skip is itself a harness
  failure, so the discipline stays two-sided.
- **Slice 2 (planned): separate verification.** Emit one Lean file per
  module with `import` lines, so an imported module's obligations are
  *not* re-checked per importer — callers consume contracts through
  Lean's own module system. The source-level design was chosen so this
  changes only the emitter/checker plumbing, not the language.
- **Deferred with slice 2+**: `pub` visibility (and `use` lists
  becoming restrictive), module subdirectories/paths in source
  (`use a::b;` as a filesystem path), re-exports.
- Whole-DAG verification means touching a leaf module re-verifies its
  dependents' obligations too when *they* are checked — acceptable now,
  the forcing function for slice 2 later.
