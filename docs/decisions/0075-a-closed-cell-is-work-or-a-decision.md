# ADR 0075 — a closed cell is work or a decision

**Decided 2026-08-17.** The type × context matrix distinguishes its two kinds
of closed cell. `not yet` is work remaining; `never` is a decision, recorded
with its reason in the `NEVER` table of `compiler/tests/type_matrix.rs` and
rendered into `docs/type-matrix.md`. The summary line now reports progress
against the cells meant to open — `63 of 163 intended; 47 never open by
design` at the time of this decision — instead of against the whole grid.

## Context

The matrix was built to make the language's sparsity measurable (one `yes`
per cell the front end admits), and its founding measurement was that most
closed cells were closed by accident — 27 of the original 50 by the parser
alone. Opening cells fixes the accidents, but the grid still conflated two
things a reader needs to tell apart: a cell nobody has earned yet, and a
cell that contradicts the language's own commitments. `option<u64>` as a
class field is the first kind. `class` as a record field is the second — a
`#[layout]` record copies freely as a value, and ownership cannot be copied.
With one kind of `no`, progress against the grid has no honest denominator,
and nothing notices when an impossible cell quietly opens.

## Decision

1. **Every `never` is written down, cell by cell, with a reason.** The
   `NEVER` table lists (context, rows, reason); the rendered matrix marks
   those cells `never` and reproduces each reason in its own section.

2. **The default for a closed cell is `not yet`.** A missing entry claims
   only that work remains, which is safe; a wrong entry would close design
   space silently. Nothing becomes a decision by omission — including new
   rows and contexts, which arrive as `not yet` until classified.

3. **A `never` cell the front end admits is a contradiction the bless flag
   cannot paper over.** The guard runs before the bless write. Reversing a
   decision is deleting its entry — with the reasoning that outgrew it — and
   blessing; the diff and this file are where the reversal is visible.

4. **A reason must survive the normative record.** A cell may be `never`
   only on grounds no ADR or design-doc section leaves open. An ADR that
   says *deferred* or *deliberately not decided* pins the cell `not yet`.

## What the first draft got wrong, and why that supports the default

The initial table claimed 54 cells; adversarial review against the ADRs
struck seven and reworded four, and every strike traced to the same error:
reading the current implementation as if it were a commitment.

- `raw element` × arrays/affine-option/class and `resource extent` ×
  affine-option/class were claimed on "not addressable bytes" and "two
  owners". ADR 0054 records *arbitrary classes in raw memory remain
  deferred* and ADR 0031 lists classes, options, and destructor-bearing
  values in typed storage as *deliberately not decided* — open questions,
  so `not yet`. The "two owners" argument was also wrong on the sealed
  operations' own semantics: `init`/`put` consume the value into the
  extent, so the token is the sole owner (ADR 0031, ADR 0053).
- `class field` × `raw<u8>` cited ADR 0024, whose class-member restriction
  ADR 0029 reversed; a pointer carries no authority (ADR 0026) and stored
  pointer fields are a planned direction (ADR 0053). `not yet`.
- The record-field reasons said "record bytes copy freely", which
  contradicts ADR 0054's explicit no-byte-representation ruling; records
  copy freely *as abstract values*, which is the fact that excludes owning
  field types. Reworded, kept.
- The cast reason named `widen` alone; the position serves `narrow` too.

Seven overclaims in a first careful draft is the argument for decision 2:
`never` earns its place through review, and everything else defaults to the
claim that cannot silently lose design space.

## What grounds the kept families

- **Integer-only constructs** (`for index`, `cast target`): the design
  defines `for` solely as range sugar over integer bounds, and the cast
  position is definitionally the `widen`/`narrow` target; pointer
  conversion already has its own spelled operation (`raw_cast`).
- **Shared borrows of copyables** (`param &`, `init param &`,
  `method param &` × integers, `bool`, value options, `record`,
  `raw<u8>`): a borrow is a second name for storage the caller keeps; a
  copyable value has no such storage role, so the borrow is observationally
  the value (ADR 0021, ADR 0072; a raw pointer is data without authority,
  ADR 0026). `&mut` of the same types stays `not yet` — write-back makes it
  a different question.
- **Owning values in record fields / consts / map keys**: record values
  copy freely (ADR 0054), constants copy freely, and a map key is
  duplicated into the ghost map's domain and compared by equality
  (ADR 0053) — each position's copying is unconditional, which is what
  excludes affine and owning types structurally rather than provisionally.
- **`const` × `raw<u8>`**: a pointer is provenance plus an offset, never an
  address (ADR 0025); no compile-time token can denote fresh provenance.

## Recorded watch items

- The borrow-family `never` expires against generics: if templates ever
  admit `&T` parameters instantiated at copyable `T`, instantiation
  collides with these cells at monomorphization. ADR 0029's lesson — an
  argument from "the language has no X" expires when X arrives — applies;
  re-read those entries when non-integer type arguments land.
- `option<raw<Record>>` is a live, admitted family (record fields, params,
  returns, locals) with no matrix row: the Option shape witness maps to
  three rows only. The grid does not currently measure it; adding the row
  is open work.
- `corpus/must-fail/option_raw_byte_pointer.sable` phrases the
  `option<raw<u8>>` refusal as a ruling while its cell reads `not yet`;
  reconcile whichever way is intended when that family is next touched.

## Consequences

Progress has an honest denominator: 63 of 163 intended cells open. The
campaign's finish line is the `not yet` count reaching zero — at which
point every cell in the grid is either open or a defended decision — and
the `never` set is itself under test in both directions: a listed cell that
opens is red, and an entry naming a nonexistent row, context, or duplicate
cell is red.
