# ADR 0019 — Module visibility: `pub`, restrictive lists, direct imports

**Decided 2026-08-10.** Implements the visibility slice ADR 0013
deferred ("`pub` visibility (and `use` lists becoming restrictive)").
Surface decisions here follow Rust's model, per the original
"Rust-familiar" ask; they are recorded for review, not yet stress-
tested by outside users.

## Decision

**Default private; `pub` exports.** `pub` marks `fn`, `class`,
`trait`, and `const` declarations. Impls and operator bindings carry no
marker: they export with the trait/class they serve. Applying `pub`
anywhere else is `module.bad_pub`.

**One line draws the boundary: the program language sees its own
module plus the `pub` items of modules it directly imports; the proof
layer sees the whole DAG.** Ghost defs, theorems, and clause text have
no visibility — the proof layer stays one flat namespace. This is not
just taste: a `pub` function's contract must elaborate for every
importer, and contracts name ghost definitions freely, so hiding the
proof layer would break the interface it documents. (Corollary: a
const referenced in *clause text* is proof-layer and always visible; a
const in *program text* is checked like any other item.)

- `use m;` imports all of `m`'s exports.
- `use m::{a, b};` imports exactly `a` and `b` — the list is now
  restrictive (v1 treated it as documentation), and every listed name
  must be `pub` (else `module.private` at the `use`).
- References resolve against direct imports only: a name exported by a
  transitive dependency is `module.not_imported` until the module
  `use`s it itself (Rust's rule; keeps a module's header an honest
  statement of what it reads).
- Referencing a non-`pub` foreign item is `module.private`, whatever
  the import shape.

**Enforcement is a loader pass** (`modules.rs::enforce_visibility`),
run on the per-module parses *before* the flat merge erases ownership:
a reference walk (calls, constructor calls, class-typed
parameters/returns/fields, trait bounds, impl heads, operator
bindings, and bare tokens naming consts) against an item index of the
whole DAG. Unknown names fall through to the checker's diagnostics
unchanged. Class-type indices resolve back to names through the same
extern table the parser was seeded with, recorded at load time.

## What deliberately did not change

- **Linking is still the flat source-level merge** (ADR 0013): private
  items still occupy their category's flat namespace, so two modules'
  same-named private runtime helpers still collide
  (`module.name_collision`). Fixing that
  needs per-module name mangling through spans, diagnostics, and the
  monitor — deferred until it hurts; visibility gates *references*,
  not existence.
- Separate verification (ADR 0018) is untouched: artifacts and name
  subtraction never depended on visibility.
- Re-exports (`pub use`) remain deferred; today that spelling is
  `module.bad_pub`.
- Class members have no per-member visibility: a `pub class` exports
  its whole interface, including field reads (ADR 0010 style).

## The sweep

The corpus gained 47 `pub` markers, found by fixpoint iteration on the
new diagnostics — every marker is a name some importer actually
references, so marker density is export density (the `mut` sweep's
discipline, ADR 0016). Guards: `module.private` (direct reference and
restrictive-list variants), `module.not_imported` (transitive
reference and outside-the-list variants), `module.bad_pub`.

## G0 namespace and nominal-type audit (2026-08-12)

The implementation now makes the namespaces implicit in this ADR explicit:

- functions, classes, and records share the flat **runtime** namespace;
- traits have their own namespace; and
- constants have their own namespace.

A restrictive `use m::{name}` remains a spelling filter across importable
program categories, so it succeeds when that module exports `name` in any of
them—including `pub const`, which the original implementation accidentally
omitted. An actual reference is then checked against its own namespace. Thus a
private trait does not hide a public runtime item with the same spelling, and a
runtime call does not acquire visibility merely because a same-named constant
is public.

The visibility reference walk now includes recursively nested use-site generic
types and exhaustively matches every checked `Ty` form that can carry a nominal
class or record. The exhaustive match is intentional: adding a new checked type
form must update visibility or fail compilation, rather than silently opening a
bypass. Imported generic-class names and arities are also recorded separately
from checked class indices, preserving the finish-order index invariant from
ADR 0013 while recursive type arguments are parsed.

Collision preflight uses module finish order and source spans before visibility
owner lookup. Consequently functions/classes/records with the same spelling in
different modules reliably produce `module.name_collision`, while equal
spellings in the distinct runtime, trait, and const namespaces remain legal.
Duplicate traits within one merged program and duplicate impl spec/method
members are likewise selected in source order by monomorphization.

None of this replaces flat linking. Private declarations still collide with a
same-namespace declaration in another module, and real per-module namespacing,
stable mangling, and re-exports remain deferred.
