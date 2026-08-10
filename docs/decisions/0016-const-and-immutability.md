# ADR 0016 — `const` declarations; locals immutable by default

Date: 2026-08-10. Status: accepted, implemented. Proposed by Alvaro
(const-by-default with an explicit mutability marker).

## Context

Contracts repeated `4611686018427387904` (2^62, the array-length
ceiling) verbatim across a dozen files, and String added more magic
numbers. Separately: in a verification language, knowing that a local
never changes is valuable to *readers* the same way it is to the
verifier — a fact established at the declaration holds everywhere,
and only marked locals ever havoc.

## Decision

**Top-level constants.**

```sable
const u64 MAX_BYTES = 4611686018427387904;
```

A named compile-time integer (literal value, optionally negated;
range-checked against the declared type — `const.out_of_range`,
`const.duplicate`). A dedicated pass substitutes every use — program
expressions by AST rewrite, clause text by the same bare-token
substitution monomorphization uses — *before* any later stage runs,
so downstream a constant is indistinguishable from the literal it
names: omega sees numerals, the monitor evaluates numerals, and the
verbatim-splice invariant is untouched. Constants export through
modules like every other item (the pass runs on the merged program).
Known sharp edge, inherited from the substitution mechanism: a ghost
binder spelled like a constant would be rewritten — same hazard as
generic parameters, same answer (don't shadow).

**Locals are immutable by default.** Mutation requires `mut` at the
declaration — marker first, C-flavor preserved, and the same word the
language already uses in `&mut`:

```sable
mut u64 lo = 0;          // assignment allowed
var mut q = Nat::from_prefix(&xs, n);   // class reassignment allowed
mut [u8] buf = b"...";   // element stores / &mut borrows allowed
```

Four enforcement points, each a named diagnostic with a must-fail
guard: assignment (`mut.assign_immutable`), element stores into owned
locals (`mut.store_immutable`), `&mut` borrows of owned locals
(`mut.borrow_immutable`), and `&mut`-method receivers
(`mut.method_immutable`). `mut` on a non-declaration is
`mut.not_a_declaration`.

- **Parameters are immutable, no marker offered.** The corpus sweep
  found zero parameter mutations; if the need appears, rebind to a
  `mut` local.
- **`&mut [T]` parameters are unaffected** — the signature is already
  the marker; stores through them stay legal.
- **`for` indices** are loop-owned: internally mutable (the
  synthesized increment), user assignment already rejected.
- **`self.f`** mutation is governed by the receiver kind
  (`&mut self`), not by local markers.

## Consequences

- The corpus sweep added 111 `mut` markers — every one marking a real
  mutation site, which is the point: the marker density *is* the
  mutation density, and everything unmarked is now a proven-constant
  read.
- 2^62 now has a name: `utf8`/`json_lex`/`json_parse` declare
  `const u64 MAX_BYTES` and their contracts read `b.len ≤ MAX_BYTES`;
  importers inherit it (test files use it through `use`).
- Two modules both defining a constant of the same name cannot be
  co-imported (`const.duplicate` on the merged program) — acceptable
  until visibility control (ADR 0013 slice 2+) gives a namespacing
  story.
- `const` values are integer literals only in v1; constant
  *expressions* (`1 << 62`) wait for a use case.
- **Open**: the inferred-declaration keyword. `var` predates
  immutability-by-default and now misnames an immutable binding;
  `let`/`let mut` (Rust: deduction + immutability connotations match
  exactly) and `auto`/`auto mut` (C++: matches the C-flavored surface)
  are the candidates. Deferred until the mild confusion becomes a
  real cost — the rename is mechanical whenever taken.
