# ADR 0026 — Lexical byte exposure

**Decided 2026-08-11.** ADR 0024 made resources a category in the
compiler; ADR 0025 put a byte heap in the machine. This decides how a
safe `[u8]` and raw memory reach each other, and it is the rung the plan
marks as the first go/no-go: *does a safe wrapper over raw memory verify
without user-visible heap logic?*

## The verdict

**Yes.** `corpus/verifies/unsafe_copy.sable`'s `copy_prefix` verifies from
a three-line value-level contract, with no heap predicate, frame clause,
separating conjunction, provenance lemma, disjointness proof, or discharge
script — and neither do the four other subjects, including one that splits
a span inside the exposure and rejoins it. 29 obligations, zero hand
proofs.

Two things carry it, and they are the decisions worth recording.

## Decision

1. **Exposure is a construct, not a proof.**
   `unsafe expose &a as (p, resource m) { ... }` lends the array's bytes
   for the body and takes them back. Entry hands the body a span whose
   bytes *are* the array's elements, all initialized, at offset 0 of a
   fresh loan allocation; exit makes the array what the bytes say. The
   bridge between the two worlds is therefore syntax with generated
   obligations, not something a user reasons about.

2. **Affinity supplies separation.**
   `raw_copy_nonoverlapping` has **no nonoverlap premise**. The two spans
   are distinct affine tokens, and that is what being distinct means. This
   was the design test the plan named: a caller who already possesses two
   exclusive resources must not have to prove they do not alias. It
   passes.

3. **Loan brands, not lifetimes.** The two bindings carry a hidden brand.
   Branded values may not be returned, assigned to a local outside the
   body, or passed to a user function — a callee could return one, and a
   brand does not survive a signature. The brand follows *provenance*
   through `raw_offset`, `split_off`, and `join`, and **not** onto loaded
   bytes: a byte read out of memory is an ordinary number. Getting that
   wrong first made `return b` illegal, which a corpus subject caught.

4. **A shared exposure cannot mutate, structurally.** Its resource binding
   is not `mut`, so `&mut m` is rejected by the ordinary
   immutable-local rule. "Shared exposure proves the bytes unchanged" is
   therefore not proved at all — there is no operation that could change
   them. That is a better answer than a frame condition.

5. **Raw operations live in `unsafe`, and the count is reported.**
   `unsafe regions: N` appears in build output. The number of places
   resting on a proof rather than on the type system is a fact about the
   program, and burying it would defeat having a boundary.

6. **`raw<u8>` only.** A wider raw element would make byte order part of
   the contract, and layout is a scheduled deliverable. Byte-at-a-time
   first, so no layout question is answered by accident.

## What the automation needed

The three findings that decided whether this rung passed. All three are
about the *shape* of what the compiler emits, not about the proof burden
on the user — which is the point.

- **The vocabulary has to be visible.** `abbrev` is not: `simp` does not
  see through a reducible definition. Every spec-level notion in
  `lean/Sable/Raw.lean` carries an explicit `@[simp]` unfolding lemma.
- **`reconstructible` had to lose its existential.** `∃ b, get k = .init b
  ∧ ...` reads better and defeats `grind`, which then has to invent a
  witness at every index. Stated as "not uninit, and its byte is in
  range", the goals are arithmetic.
- **A store's effect has to be functional, not axiomatic.** As a
  conjunction of "index `k` is now this, every other index is unchanged",
  every exit obligation left `grind` doing case analysis and timing out.
  As `m₂ = write m k (.init w)`, the composition lemmas fire on the shape.

**Reconstructibility is tracked as a hypothesis, not proved at each step.**
It is the whole condition for handing bytes back — every byte present, and
every one a real `u8` — and it is assumed after each operation because the
*operation* establishes it, with the theorem named at each site. This is
the treatment array length and element ranges already get across a store
(`vcgen.rs`: "stores are the only mutation and preserve length and element
ranges by construction"). One lemma per operation — `ofSeq`, `write`,
`take`, `drop`, `cat` — is the entire cost of keeping the exit automatic,
and it is why a `split_off` inside an exposure does not make the wrapper
proof-noisy.

## Consequences

- `Ty::Raw(IntTy)` and `Val::Ptr` join the value plane; a pointer is
  `Sable.RawPtr` in the logic, carries no authority, and is data like any
  other. Every raw operation pairs a pointer with a resource borrow: the
  pointer says *which* byte, the resource says the caller may touch it.
- Raw operations carry a *pointer-names-byte* premise
  (`SpanView.namesByte`) rather than a global provenance predicate: same
  allocation, offset lands inside the span.
- **The exposure's exit obligation is currently unfalsifiable, and that is
  recorded rather than hidden.** Every operation in the U4 surface
  preserves reconstructibility, so `expose.<a>.bytes` always closes. What
  will make it bite is `take8`, which leaves a byte uninitialized — it is
  in the machine (ADR 0025) but not in the surface, and adding it needs a
  strengthened `write_reconstructible`. The plan's negative subject "read
  an uninitialized byte" is unreachable until then; the guard that exists
  instead is `load8_init`, which is a real obligation on every load.
- U3's two inherited exit criteria are now met: `svm.rs` lowers exposure
  to the machine's own loan-allocation model (allocate, copy in, run, copy
  back, release), `corpus/svm-diff` has a valid and an invalid raw
  subject, and an injected wrong lowering diverges. The interpreter's raw
  failures classify as `undef` while keeping a precise message, which is
  the licence ADR 0025 granted.
- A stale warm `sable daemon` serves the old prelude after a `lake build`.
  This cost real time during this rung. Not fixed here; recorded because
  it will cost it again.

## Deliberately not decided

- **`take8` in the surface**, and with it a falsifiable initialization
  obligation.
- **A machine `expose` primitive.** Lowering spells the model out instead,
  which keeps the normative machine smaller; the plan permits either.
- **Nested exposure of overlapping arrays.** Two exposures of the *same*
  array would produce two loans of one buffer. Nothing prevents it today
  because the exposed array is borrowed, and a second mutable borrow of it
  is already rejected — but that argument leans on the borrow rules rather
  than on the exposure rules, and it should be stated as its own check
  before allocators arrive.
