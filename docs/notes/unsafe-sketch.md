# Unsafe Sable — the design argument

*Companion to design §5 (the boundary as adoption gate), §9 (the escape
ladder), §11 (profiles and machine models), and the goals document's
allocator benchmark ("the real deliverable is the design of unsafe
Sable").*

*This is the **argument** half of a pair. It says what the problem is,
why this decomposition rather than another, and what is still open to
taste. The **specification** — resource types, syntax, machine changes,
milestones U1–U10, corpus, exit criteria — is
`docs/notes/unsafe-plan.md`. Read this one to disagree with the design;
read that one to build it. Neither is implemented; when the U1 probe
concludes, the chosen interpretation becomes an ADR that supersedes both
on the points it decides.*

*Provenance: a first draft argued from systems examples (Claude); an
external design review (GPT-5.6) proposed the affine-resource
architecture, which was better than the first draft and is the spine
here; a synthesis; then a specification round and a review of it. Where
the rounds disagreed, the disagreement is recorded rather than smoothed
over.*

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
everything else — but the machine grows first. The first concurrent
benchmark should be an SPSC queue, not a spinlock smuggled into a
sequential model.

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

This classification answers "why does systems code reach for `unsafe`."
It is orthogonal to, and does not replace, the question "which Sable
mechanism is involved" — verified unsafe code, machine intrinsic, or
external contract. Both classifications earn their keep; the plan
carries the second, this note carries the first.

## The spine: a verified resource sublanguage

> A raw pointer says **where**.
> A resource says **what authority the program owns and what state it
> is in**.
> A contract says **how an operation transforms that authority**.
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
are checked. Core resources: ownership of raw bytes, ownership of one
typed location, authority to release a root allocation, and — the
refinement the allocator forces — an allocator-specific *lease* for a
suballocated block, which is emphatically not a free token.

Splitting deallocation authority from contents is load-bearing: an
allocation may be carved into many subregions, and none of them may
thereby acquire permission to free itself. Verus's `vstd::raw_ptr`
library independently arrives at nearly the same factoring — separate
typed and raw access permissions, initialization state in the
permission rather than the pointer, a distinct deallocation permission
returned alongside memory authority at allocation. That is
corroboration rather than proof, but two designs reaching the same
split from different starting points is evidence it is forced by the
problem rather than chosen by taste.

**Affine, not linear.** A resource may be abandoned; that leaks, and a
leak is not a safety failure. Memory safety must not depend on
mandatory cleanup. `#[must_consume]` can diagnose leaks later as a
separate, weaker guarantee — the two must not be conflated.

**A package with verified unsafe code and no assumptions is fully
verified.** Unsafe is an audit surface, not a trust gap; the status
line should say so, and separate the categories — unsafe blocks,
unsafe interfaces, external contracts, assumes, defers — so that
"fully verified" never appears next to an unproved extern contract.

Raw pointers carry no ownership and one type, `raw<T>`: read/write
authority comes from the accompanying resource, so the pointer itself
is freely copyable and harmless. It denotes **provenance + offset**,
not an address — two pointers may share a machine address and refer to
different allocations after reuse. Creating a pointer never creates a
resource.

## Affinity without separation logic in the evidence layer

This is the piece the review flagged as "prototype this first," and the
answer it converged on is cleaner than a Lean separation-logic
embedding — clean enough to be the design's main bet.

> **Authority is a checker property. Resource state is a Lean value.
> The soundness theorem connects them.**

An earlier draft of this note said something stronger and wrong —
"affinity and provability never meet." They do meet, in the
metatheorem, and the sharper statement matters because the wrong one
implies an implementation the architecture forbids. The checker
maintains an affine context of live authorities. Lean never receives
those authorities as propositions; it receives each resource's **view**
— ordinary pure projections (`span.ptr`, `span.bytes`, `cell.state`,
`lease.allocator`). Facts about a view are knowledge, and knowledge is
freely duplicable: copying the fact that a cell is initialized does not
copy the authority to touch it. So there is no `PointsTo p v`
proposition, no `*`, no frame rule, no bunched implication in any
clause a user writes or reads.

The division of labor is exact, and it has to be, because Sable's
central invariant is that proof text is spliced verbatim and the Rust
side never interprets it. **The compiler rejects repeated consuming
*program* uses of a resource token. It does not, and must not, police
how often `span` appears on a `///` line.** The first draft claimed the
dangerous inference was "impossible to express" because the checker
would reject mentioning a resource twice — that would require the Rust
side to parse Lean, which it does not do and should never do. What is
impossible is *obtaining* the second authority, not *writing* the
second occurrence.

The substrate exists. `check.rs` already runs a flow-sensitive
per-place state machine for definite initialization and affinity (ADR
0020/0021), and every negative example below is a *typechecker* error
with a source span and a name — not a failed SMT query, and not a Lean
goal about a global heap. What does not yet exist is a real engine: the
current `moved` bit is adequate for whole local class values and
nothing more, which is why the plan builds a place-and-borrow engine on
ordinary classes before resources need it.

Where does it break? A statically unknown *number* of resources — the
intrusive list's per-node permissions. The answer is not to reach for
separation logic but to make the aggregate a **single affine token
holding a Lean map**, with sealed `take`/`put`/`borrow` as the only way
in and out. But note the honest correction: interior disjointness does
**not** follow merely from the map being a function. It follows from
the hidden interpretation of the aggregate token as the valid
composition of the resources it contains. That is where the separating
structure lives, and it lives there invisibly.

Separation logic still exists — in the **soundness metatheorem**
relating the resource discipline to the raw heap, where `*` belongs.
Users never write it. Evidence blocks never contain it. This is the
same division of labor that makes safe Sable readable: ownership is a
type-system fact, and the logic reasons about values.

**The place this bet is most likely to fail is loops.** At a loop head
Sable's havoc discards facts and re-establishes only the invariants, so
nothing in the goal says two live tokens still describe disjoint
authority on the second iteration. That has to follow from shape
equality at the backedge preserving the interpretation — which makes it
a theorem to prove, not a rule to assert. A carving loop is therefore
part of the first probe, not a later refinement.

## What the machine grows

The SVM gains a **raw heap** alongside the existing value world, with
allocations carrying id, size, alignment, liveness, and initialization
state; `raw<T>` is (allocation id, offset); freeing marks an allocation
dead so a stale pointer keeps its old provenance and can never alias a
later reuse. Every existing safe rule frames the raw heap unchanged —
the same absorb-without-disturbing extension the machine took twice
already (capacity; frames), each time with agreement, determinism, and
progress re-proven.

Raw storage is not a `seq u8`. Uninitialized is a distinct byte state,
and for typed storage `uninit | init(T)` must not be encoded as
`option<T>`: an initialized `option<U>` holding `none` has to stay
distinguishable from storage that was never written.

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
  **not** a typed cell with a volatile flag.

Every raw operation stays total: it succeeds or reaches `trapped`/
`undef`, and verified programs prove the bad outcomes unreachable. The
soundness statement survives verbatim — *verified programs never reach
`undef`* — with a larger, explicitly enumerated axiom set. The
differential harness can then test invalid accesses too, which is how
the negative corpus stays honest.

## Trust, and where it is visible

`extern` declarations carry full contracts plus a mandatory audit
payload (the `assume` precedent: the reason string is not optional).
Crucially, effects are stated **structurally, through resource
parameters**, not as a free-form global `modifies` clause: only passed
mutable resources may change, and a foreign function that touches
global state must receive an explicit world capability. The foreign
implementation is trusted to respect an ownership-shaped contract —
which is a much smaller thing to trust than an arbitrary frame formula.
Foreign pointer arguments are `noescape` by default, so the compiler
can expose a safe slice for the duration of the call and reclaim it
immediately after.

Because contracts are machine objects, the compiler can compute, per
module, the transitive set of boundary axioms its verification rests
on — a **trust manifest**. `unsafe` is the *local* audit marker; the
manifest is the *global* one, and only the manifest answers "what does
this export actually depend on." For a language where LLMs write most
of the code, the manifest is the artifact the human reviews. It has to
be hashed into the content-addressed artifact rather than stored
beside it (ADR 0018): an artifact must not outlive a change to what it
trusted.

Trust also gets an alternative to itself: `extern` contracts are
assumptions *unless the foreign implementation ships an imported
proof*, which is the hook for verified-library interop later.

Resources are more general than memory, and file descriptors are the
cheap demonstration — an affine `OpenFile` that `close` consumes
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

## What the probes are meant to falsify

The architecture is a bet, and these are the specific ways it could
lose. Each is an exit criterion in the plan, phrased here as the
failure it is looking for.

1. **View contracts are not concise.** If stating what `split_off` does
   takes a paragraph of view algebra, the abstraction is not paying for
   itself.
2. **Separation leaks into user clauses.** If the hidden interpretation
   cannot establish disjointness without `*` appearing somewhere a user
   reads, the main bet has failed.
3. **Loops leak it too.** If a carving loop's invariants have to
   restate hidden separation facts, the bet fails in the place most
   real allocator code lives.
4. **Aggregates only work for hand-picked finite lists.** The intrusive
   list is the exam; a wall of explicit resource rearrangement is the
   failing grade.
5. **`copy_prefix` is proof-noisy.** The smallest useful vertical slice
   should have a two-line value-level spec and no user-visible heap
   predicate. If it does not, nothing above it will.

The response to any of these is to simplify or strengthen the resource
abstraction — not to expose general separation logic prematurely, and
not to widen `assume`.

## Open questions (taste, explicitly)

1. **Is `unsafe {}` worth writing if it grants nothing logical?**
   Settled: `unsafe` grants no authority and waives no obligation. Not
   settled: whether the lexical marker earns its weight, or whether the
   unsafe surface should be derived entirely. Position taken, and
   provisional through the FFI milestone — keep the block, because it
   does grant something operational (access to a restricted
   vocabulary), while deriving everything that could go stale (unsafe
   interfaces from signatures, trust dependencies from the call graph,
   unnecessary blocks from their contents). The counterargument stands:
   a marker that confers nothing is a lint, and lints should be derived
   so they cannot lie.
2. **Trust payload shape**: reason string only (the `assume`
   precedent), or structured fields (ABI, layout, alignment,
   provenance) that tooling can act on?
3. **Oracle scripting in `sable test`**: per-test scripts, or a
   world-stub module convention? Decides how pleasant driver testing
   is; deserves its own round with example 1 implemented.
4. **How much of the trace is contract-visible.** Full event lists
   compose awkwardly; drivers likely want trace *projections* ("the
   writes to UART0 are…") as ghost functions over the trace — unproven.
5. **Pointer equality across allocations.** Ordering and subtraction
   need common provenance; live cross-allocation equality is the open
   one, and the intrusive list is what should decide it. Restricting
   the first list to nodes carved from one arena sidesteps it, which
   may be the right v1 answer or may be hiding the question.
6. **Mandatory cleanup.** Affine authority buys safety; linear or
   `#[must_consume]` buys leak freedom. Which resources deserve the
   stronger discipline is unresolved, and the two must not be
   conflated into one keyword.

## The bottom line

> **Make raw pointers useless without affine erased resources, and make
> those resources visible to Lean only through pure views.**

The repository has already validated the first half of the checker
story at a smaller scale: affine moves are source-level flow facts with
spans, and the logic reasons about the same class value whether it
arrived by borrow or by move (ADR 0020), with the flow facts precise
enough to follow control flow (ADR 0021). The next argument should be
executable. Start with the concrete Lean probe — including the loop —
then the place engine, then a byte-only vertical slice, and stop at
`copy_prefix` long enough to judge whether the abstraction really
preserves Sable's readability.
