# ADR 0022 — The resource-context interpretation

**Decided 2026-08-11**, on the evidence of `docs/notes/unsafe-probe.lean`
(U1). This fixes the metatheory unsafe Sable will be built against, so
that compiler work (U2a onward) encodes a chosen model rather than
guessing at one. It decides the *interpretation*, not the surface
syntax.

## Context

Unsafe Sable's central bet is that authority can be a checker property
while the logic reasons only about pure values (`docs/notes/unsafe-sketch.md`).
That bet needs a theorem: something connecting the affine context the
Rust side maintains to the raw heap the machine has. Without it, the
loop rule in particular is an assertion — at a loop head, havoc discards
facts and re-establishes only the invariants, so nothing in the goal
says two live tokens still describe disjoint authority on the second
iteration.

## Decision

**The interpretation is `Own(rawHeap, Δ)`: every resource in the context
agrees with the heap, and the resources are pairwise disjoint over an
explicit capability space.**

Four commitments, each validated by a proof in the probe:

1. **Capabilities are the unit of authority, and byte access is separate
   from deallocation.** `Cap := byte(alloc, offset) | free(alloc)`.
   Carving a span can never mint the right to free what it was carved
   from, because `split_off` only ever redistributes `byte` caps.

2. **Backing is stated per byte.** A span's view claims, *for each index
   it covers*, that the heap has that byte in a live allocation, in
   bounds, with the recorded contents. This is the load-bearing choice
   and the obvious alternative is wrong: one existential covering
   `[off, off+len)` makes an **empty** span assert that its allocation is
   live, and `free` then breaks — a zero-length residual span owns no
   capability, so disjointness cannot exclude it, yet it stops agreeing.
   Per-byte backing makes empty spans vacuously backed: no authority, no
   constraint. Split and join reduce to index arithmetic as a
   consequence.

3. **Views are ordinary values; authority never appears in Lean.** A
   resource's view is a plain structure (`alloc`, `off`, `len`, `bytes`),
   and facts about it are duplicable knowledge. The interpretation is the
   metatheory's object: no generated VC receives it as a hypothesis, and
   no user clause mentions `Own`, disjointness, or the heap.

4. **Aggregate resources carry their own disjointness.** A dynamic
   collection is one affine token holding a total map plus a `keys`
   predicate — nothing finite or enumerated. Its interpretation has two
   conjuncts: every contained resource agrees, **and** they are pairwise
   disjoint. The second does *not* follow from the map being a function,
   which an earlier draft of the sketch claimed; `put` needs it as a
   premise it cannot reconstruct.

## What the probe established

Preservation is proved for `split_off`, `join`, `load8` (soundness: the
machine returns what the view says), `store8`, `take8`, `allocate`, and
`free`, plus an aggregate `take`/`put` round trip. No `sorry`, and no
`Classical.choice`.

Two results decide how the compiler should be built:

**The loop rule is not new metatheory.** `own_carve_step` — the backedge
obligation for a loop that carves one byte per iteration, transforms it,
and joins it onto the processed prefix — is proved by *composing* the
primitive rules with two context-reordering lemmas. Nothing bespoke. So
the checker's loop rule is "resource shape at the backedge equals the
shape at the head," and the induction over iterations is standard. The
value-level invariant a user writes (`carve_views_step`) mentions no
heap and no disjointness.

**Freeing derives its own side condition.** `own_free` does not take
"nothing else touches this allocation" as a hypothesis. It follows from
the consumed span covering the allocation and being disjoint from
everything else — the affine discipline paying for itself, which is the
whole architecture in one theorem.

**The views are automation-friendly.** Five goals shaped the way vcgen
emits them — view fields as binders, callee posts as hypotheses, guarded
quantifiers, everything `Int` — close under `sable_auto` at the
production heartbeat budget (ADR 0011) with no budget warnings. The
probe elaborates in about 1.7 seconds.

## Consequences

- **The context is a set, not a sequence.** The probe's `Own` is a list
  and the primitive rules act on its head, so the carving loop needed
  two reordering lemmas as pure bookkeeping. U2b should represent the
  live context unordered, or state the rules positionally; reproducing
  the list shape would import the noise into the compiler.
- **Capability space is where new resource kinds land.** Adding
  allocator leases, open files, or MMIO regions means adding `Cap`
  constructors and their `owns`/`agrees` cases. Nothing in the framing
  or disjointness machinery changes — `Disjoint.mono_left` and the
  per-byte frame lemma are kind-agnostic.
- **The heap needs one well-formedness condition**: allocation ids at or
  above the fresh counter are unallocated. That is what makes a new
  allocation disjoint from every live resource without inspecting the
  context, and it is the only global heap invariant the model requires.

## Deliberately not decided

- **Abstract typed storage.** The probe is byte-only, so U1's question 5
  is unanswered. The model has room — `Allocation.bytes` is consulted
  only through the backing predicate, so a typed extent kind is one new
  case there and touches no span theorem — but the Lean encoding of a
  heterogeneous typed extent is a real modelling question and gets its
  own probe before U7b.
- Surface syntax for resources, which stays provisional through U2b.
- Whether the interpretation graduates from `docs/notes/` into
  `lean/Sable/`. It does so when the compiler emits against it, not
  before.
