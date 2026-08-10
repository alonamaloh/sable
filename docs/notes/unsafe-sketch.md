# Unsafe Sable — a design sketch

*Companion to design §5 (the boundary as adoption gate), §9 (the escape
ladder), §11 (profiles and machine models), and the goals document's
allocator benchmark ("the real deliverable is the design of unsafe
Sable"). Nothing here is implemented; this note exists to be argued
with.*

*Provenance: a first draft argued from systems examples; an external
design review (GPT-5.6) proposed the affine-resource architecture,
which is better than what the first draft had and is adopted here as
the spine. This version is the synthesis, including the places the two
disagree — those are flagged, not smoothed over.*

## Six examples, and what each actually needs

**1. A UART driver (MMIO).** Write bytes to a device register at a
fixed address; poll a status register. Needs: memory the type system
never allocated; *volatile* semantics — every access is an observable
effect, reads are not pure (the device has its own state machine), and
neither elision nor reordering is permitted. The correctness claim
worth stating is about the *sequence of accesses*, not about values in
memory.

**2. `read(2)`, or any FFI call.** Call code Sable cannot see. Needs: a
foreign function with a stated contract that Sable takes on faith, and
an ABI story for the arguments. Note what the contract must contain
that safe Sable never writes: an explicit *frame clause*. Inside the
language framing is free — ownership makes it a type fact (pillar 3).
A foreign callee is outside the ownership discipline, so its frame must
be stated, and it is part of what is trusted.

**3. The allocator** (the goals document's forcing benchmark). Carve a
region into blocks, hand out an owned buffer that aliases nothing,
accept it back, reuse the bytes. Needs disjoint sub-ownership of a byte
range that can be split, transferred through a contract, and returned.
This is the deep end; everything else here is shallower than Rust's
equivalent, this one is not.

**4. Parsing a packet header in place.** In C or Rust this is pointer
casting; **in Sable it is already safe code** — indexing plus
arithmetic, with the representation relation stated as a ghost function
(the utf8/varint/hex corpus pattern, contracts and all). A zero-copy
typed view is a lowering optimization, not an expressiveness gap. Worth
saying out loud: a large fraction of what forces `unsafe` in Rust is
reinterpretation, and reinterpretation over value semantics is just
arithmetic.

**5. Page tables and privileged state.** Write CR3, invalidate a TLB
entry, mask interrupts. Same shape as MMIO (effects, ordering), plus
§11's alternative-machine story: against a Sail RISC-V model these are
contracted intrinsics specified against *that* model — the seL4
architecture with Sable in place of C.

**6. A spinlock.** Needs a concurrent machine model. The SVM is
sequential and no boundary construct papers over that. Named so its
absence is a decision: concurrency is its own machine extension (§12),
and atomics will follow the same contracted-intrinsic pattern as
everything else — but the machine grows first.

## Rust's `unsafe` is three things wearing one keyword

1. **Trust** — axioms about the world: "this C function does what its
   man page says," "this address range is the UART."
2. **Model** — operations on state the type system does not govern:
   raw memory, device registers, privileged state.
3. **Evidence** — invariants the compiler cannot check.

Rust discharges all three with one keyword and a comment convention.
Sable already has (3), and better: the §9 ladder, where obligations are
first-class objects, `defer` means "check it at runtime," and `assume`
is a named, audited, tallied axiom. So the design problem is (1) and
(2) — and the central claim of this note is that (2) should be *typed*,
not trusted.

## The spine: a verified resource sublanguage

> A raw pointer says **where**.
> A resource says **what memory you own and what state it is in**.
> A contract says **how an operation transforms that resource**.
> `unsafe` marks the audit surface and confers **no** logical authority.
> `extern` and `assume` are where trust actually enters.

Sable gains a third value category:

```text
program value    runtime, affine by ordinary ownership
ghost value      erased, freely duplicable
resource value   erased, affine
```

A resource cannot be copied or fabricated. It is moved, borrowed,
split, joined, or transformed by operations whose resource contracts
are checked. Core resources:

```text
RawSpan(p, n, bytes)          ownership of n raw bytes at p
PointsTo<T>(p, state)         ownership of one typed location
Dealloc(allocation, layout)   authority to release an allocation
```

Splitting `Dealloc` from contents is load-bearing: an allocation may be
carved into many subregions, and none of them may thereby acquire
permission to free itself. (Verus's raw-pointer library converged on
the same decomposition; treat that as evidence the factoring is
forced, not stylistic.)

`unsafe { … }` makes raw intrinsics *available*; it does not make them
*legal*. `read_copy(p, cell)` is legal because the caller holds a
`PointsTo` whose `ptr` is `p` and whose state is initialized — an
ordinary precondition, discharged the ordinary way. Consequently
`unsafe` must never permit an `assume`, fabricate a resource, suppress
a VC, or turn an invalid access into unchecked native behavior.

**A package with verified unsafe code and no assumptions is fully
verified.** Unsafe is an audit surface, not a trust gap; the status
line should say so, and separate the categories:

```text
unsafe blocks:       14  (all resource obligations proved)
unsafe interfaces:    3
external contracts:   2  (audited assumptions, listed)
assumes:              0
defers:               0
```

Raw pointers carry no ownership and one type, `raw<T>`: read/write
authority comes from the accompanying resource, so the pointer itself
is freely copyable and harmless. It denotes **provenance + offset**,
not an address — two pointers may share a machine address and refer to
different allocations after reuse. v1 restrictions: no
integer-to-pointer round trip, arithmetic preserves provenance,
comparison requires a common allocation, `option<raw<T>>` instead of
null, `raw<u8> → raw<T>` requires alignment/size plus a resource
transformation, and **creating a pointer never creates a resource**.

## Affinity without separation logic in the evidence layer

This is the piece the review flagged as "prototype this first," and I
think it has a cleaner answer than a Lean separation-logic
embedding — clean enough to be the design's main bet.

**Affinity is a checker property; provability is a Lean property. They
never meet.** Resources are checked affine by the Rust-side
typechecker, and they *do not appear in Lean as hypotheses at all*.
What appears in contracts is a resource's **view**: ordinary pure
projections (`cell.ptr`, `cell.initialized`, `cell.value`,
`span.bytes`). Lean sees opaque values with fields and reasons about
them with the mathematics it already has. There is no `PointsTo p v`
proposition, no `*`, no frame rule, no bunched implication in any
clause a user writes or reads.

This works because the dangerous inference — *using the same ownership
twice* — is impossible to express, not merely false: to state it you
would need to mention a resource variable twice, and the checker
rejects that before Lean is invoked. Disjointness facts arrive as
*consequences of the affine discipline*, not as proof obligations.

The substrate exists. `check.rs` already runs a flow-sensitive
per-variable state machine (`VarInfo { ty, initialized, mutable }`) for
definite initialization; affine tracking adds one state (*consumed*)
and the rule that consuming a resource variable requires it live and
leaves it dead. Every diagnostic in the negative corpus below
(duplicate a `PointsTo`, use after deallocation, read after `take`) is
then a *typechecker* error with a source span and a name — not a failed
SMT query, and not a Lean goal about a global heap.

Where does it break? A statically unknown *number* of resources — the
intrusive list's per-node permissions. The answer is not to reach for
separation logic but to make the aggregate a **single affine token
holding a Lean `Map`**, with `take`/`put` as the only way in and out.
Interior disjointness is then a consequence of the map being a function
— ordinary Lean mathematics, no new logic. The intrusive-list benchmark
exists precisely to test whether that holds up; if extraction and
reinsertion turn into a wall of rearrangement, that is the signal to
improve the resource layer, not to paper over it with tactics.

Separation logic still exists — in the **soundness metatheorem**
relating the resource discipline to the raw heap, where `*` belongs.
Users never write it. Evidence blocks never contain it. This is the
same division of labor that makes safe Sable readable: ownership is a
type-system fact, and the logic reasons about values.

## What the machine grows

The SVM gains a **raw heap** alongside the existing value world:

```text
Config = code × frames × rawHeap × trace × …
```

with allocations carrying id, size, alignment, liveness, and
initialization state; `raw<T>` is `(allocation id, offset)`; freeing
marks an allocation dead so a stale pointer keeps its old provenance
and can never alias a later reuse. Every existing safe rule simply
frames the raw heap unchanged — the same absorb-without-disturbing
extension the machine took twice already (capacity; frames), each time
with agreement/determinism/progress re-proven.

**Resources are erased, so they are not in the configuration at all.**
The machine has a heap; the resource layer is a static discipline; the
soundness theorem connects them. That split is what keeps the machine
small and the interpreter honest.

Two further extensions, both reusing precedent:

- **Lexical exposure.** `unsafe expose &mut buf as (ptr, resource r) { … }`
  temporarily opens a safe array's value representation into a raw
  block, requires the whole resource back at block exit, reconstructs
  the value, and forbids the pointer from escaping. Semantically it
  allocates-and-reconstructs; a native backend compiles it to taking
  the address. This avoids Rust-style lifetimes for v1: long-lived raw
  pointers must point into explicitly allocated stable storage.
- **Devices as trace + oracle.** Volatile accesses are events appended
  to a `trace` component, and device reads draw values from an **input
  oracle** the machine is parameterized by. This is the `cap` move
  repeated (ADR 0005 res. 7): where "allocation may fail" threatened
  determinism, a capacity parameter restored it; where "device reads
  return anything" threatens it, an oracle parameter restores it, and
  soundness quantifies over the oracle. Driver correctness then becomes
  a *trace predicate* — example 1's "emits exactly this sequence" is a
  short, device-independent `post`. A device register is emphatically
  **not** a `PointsTo<u32>` with a volatile flag.

Every raw operation stays total: it succeeds or reaches `trapped`/
`undef`, and verified programs prove the bad outcomes unreachable. The
soundness statement survives verbatim — *verified programs never reach
`undef`* — with a larger, explicitly enumerated axiom set. The
differential harness can then test invalid accesses too, which is how
the negative corpus stays honest.

## Trust, and where it is visible

`extern` declarations carry full contracts plus a mandatory audit
payload (the `assume` precedent: the reason string is not optional) and
an explicit frame clause; call sites owe the pres and gain the posts,
using the call machinery that already exists. Foreign pointer arguments
are `noescape` by default, so the compiler can expose a safe slice for
the duration of the call and reclaim it immediately after.

Because contracts are machine objects, the compiler can compute, per
exported function, the transitive set of boundary axioms its
verification rests on — a **trust manifest**. `unsafe` is the *local*
audit marker; the manifest is the *global* one, and only the manifest
answers "what does this export actually depend on." For a language
where LLMs write most of the code, the manifest is the artifact the
human reviews.

Trust also gets an alternative to itself: `extern` contracts are
assumptions *unless the foreign implementation ships an imported
proof*, which is the hook for verified-library interop later.

Resources are more general than memory, and file descriptors are the
cheap demonstration: `class File { i32 fd; /// resource open : OpenFile fd }`,
where `close` consumes the resource and the destructor invokes it
exactly once.

## Monitorability

`sable test` runs boundary code against a **scripted world**: stub
externs, scripted oracles, and the same dynamic contract checking as
everywhere else. Because the interpreter can carry shadow metadata it
can also detect provenance, liveness, and double-ownership violations
dynamically — so the negative corpus is executable, not just a
compile-error list.

This does **not** make those properties `defer`-able. `defer` is
restricted to the runtime-monitorable fragment because native code must
be able to check it, and native code cannot track provenance without
shadow state it should not be made to pay for. Sanitizer-detectable ≠
release-monitorable, and the ladder should keep the distinction sharp.

## Prerequisites — the sequencing finding

The resource design is written in a Sable that does not exist yet.
`class Box<T> { raw<T> ptr; /// resource cell : … }` needs **class-valued
fields**; `split(region) -> pair<Region, Region>` needs **moves** and a
product type; `RawRegion` methods that consume `self` need **by-value
class parameters**. All of these are ADR 0010's explicitly deferred
slice B (moves, `&mut C`, class-valued fields).

So: **unsafe v1 is blocked on finishing first-class class values**, and
the deep reason is one thing, not three — ownership must mature from
*locals* to *places* (sub-parts of owned things, with their own
ownership, transferable independently). Resource carving is that same
notion at byte granularity. Whichever lands first digs the foundation
the other builds on, and class values is the one with a milestone
(`Integer`) already waiting on it.

## The ladder

Ordering differs from the review's in one deliberate place, flagged
below.

0. **Class values slice B** (moves, class-valued fields, `&mut C`) — the
   prerequisite above.
1. **Lean prototype of the resource layer.** A tiny raw heap,
   `RawSpan`/`PointsTo`/`Dealloc`, and the split/join/read/write/init/
   free rules, proven before compiler work — the probe-first rule that
   has paid every time (bignum, hashmap, Algorithm D). The specific
   question it must answer: do resource *views* generate tractable
   goals, and does the affine-token-plus-`Map` trick hold for
   aggregates?
2. **Safe buffer split + copy.** `copy_prefix(&[u8] src, &mut [u8] dst)`
   implemented through lexical exposure. Tests exposure, provenance,
   splitting, read-vs-write authority, nonoverlap, frame conditions,
   reconstruction, and nonescape — all in one small example with a
   two-line spec. Do not proceed until it is clean.
3. **FFI: `read`/`write`/`close` with safe wrappers.** *(Moved up from
   the review's #5.)* It needs only exposure plus extern contracts — no
   `Dealloc`, no typed `PointsTo`, no allocator — and design §5 calls
   the FFI boundary the gate between research artifact and usable
   language. Making the adoption gate wait behind three substantial
   verification projects is the wrong risk order.
4. **Static bump arena.** Program-lifetime region, so arena-outlives-
   allocation never arises. Invariant: `allocated prefix * unused suffix
   = original region`. Design criterion: *if the arena has to sit inside
   one large unsafe block, the resource API is too weak* — only root
   acquisition, typed conversion, and raw loads/stores should be
   visibly unsafe.
5. **In-band free-list allocator.** Metadata inside free blocks, not an
   auxiliary safe vector: bytes changing roles between allocator
   metadata, uninitialized storage, and typed objects is the
   informative part. This is what justifies separate `Dealloc`
   authority, provenance, and joining rules.
6. **Intrusive doubly linked list.** The aggregate-resource exam
   described above; the go/no-go for the affine-token design.
7. **MMIO and privileged state**, as a semantic layer (trace + oracle),
   not as heap access.

Excluded from v1, deliberately: integer-to-pointer conversion, escaping
pointers to movable locals, general `transmute`, unions/packed structs,
bytewise copies of pointer-containing values, retained foreign pointers
and callbacks, atomics/DMA/shared raw memory, and `defer` for
liveness/provenance/ownership obligations.

Negative corpus (each must be a *named diagnostic*, most of them from
the typechecker): duplicate a `PointsTo`; read before initialization;
read after `take`; use a pointer after deallocation; deallocate a
subregion; free through the wrong allocator; join nonadjacent regions;
overlapping `copy_nonoverlapping`; return a pointer from `expose`;
construct ownership from an integer.

## Layout as law-carrying concepts

Raw memory forces an explicit layout interface, and ADR 0009's concepts
are the right shape for it: `size_of`, `align_of`, and
`represents : seq u8 → T → Prop` as spec functions, with laws (align is
a nonzero power of two; representations have length `size_of`;
representation is functional). Separate concepts for separate powers —
`RawStorable`, `BitwiseCopyable`, `FromBytes`, `Zeroable`, `CRepr` —
because they are different mathematical claims. v1 supports integers,
arrays of supported elements, and explicitly laid-out records; not
arbitrary classes, references, destructor-bearing values, unions, or
packed structs.

## Open questions (taste, explicitly)

1. **Is `unsafe {}` worth writing if it grants nothing?** Position
   taken: yes, as a local audit marker, paired with the derived global
   manifest. The counterargument — a marker that confers no authority
   is a lint, and lints should be derived so they cannot lie — is not
   obviously wrong.
2. **Trust payload shape**: reason string only (the `assume`
   precedent), or structured fields (ABI, layout, alignment,
   provenance) that tooling can act on?
3. **Oracle scripting in `sable test`**: per-test scripts, or a
   world-stub module convention? Decides how pleasant driver testing
   is; deserves its own round with example 1 implemented.
4. **How much of the trace is contract-visible.** Full event lists
   compose awkwardly; drivers likely want trace *projections* ("the
   writes to UART0 are…") as ghost functions over the trace — unproven.
5. **Alignment in the model.** Regions are byte arrays; alignment is a
   lowering concern until it is a proof concern. Where does it enter?
