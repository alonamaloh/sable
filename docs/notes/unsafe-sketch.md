# Unsafe Sable — a design sketch

*Method: realistic systems-programming examples first, framework second.
Companion to design §5 (the boundary as adoption gate), §9 (the escape
ladder), §11 (profiles and machine models), and the goals document's
allocator benchmark ("the real deliverable is the design of unsafe
Sable"). Nothing here is implemented; this note exists to be argued
with.*

## Six examples, and what each actually needs

**1. A UART driver (MMIO).** Write bytes to a device register at a
fixed physical address; poll a status register. Needs: access to memory
the type system never allocated, at addresses fixed by a datasheet;
*volatile* semantics — every access is an observable effect, reads are
not pure (the device has its own state machine), and the compiler may
neither elide nor reorder them. Correctness worth stating: "the driver
emits exactly this initialization sequence, then one write per byte" —
a claim about the *sequence of accesses*, not about values in memory.

**2. `read(2)`, or any FFI call.** Call code Sable cannot see. Needs: a
foreign function with a stated contract ("returns `r ≤ n`; the first
`r` bytes of `buf` are overwritten; **nothing else changes**") that
Sable must take on faith, and a layout/ABI story for the arguments.
Note what the contract must contain that safe Sable never writes: an
explicit *frame clause*. Inside the language, framing is free —
ownership makes it a type fact (pillar 3). A foreign callee is outside
the ownership discipline, so its frame must be stated, and it is part
of what is trusted.

**3. The allocator itself** (the goals document's forcing benchmark).
Manufacture ownership from raw bytes: carve a heap region into blocks,
hand out an owned `[u8]` that aliases nothing, accept it back, reuse
the bytes. Needs: a notion of *disjoint sub-ownership of a byte range*
that can be split off, transferred through a contract, and returned.
This is the deep end — everything else in this note is shallower than
Rust's equivalent, this one is not.

**4. Parsing a packet header in place.** Read an Ethernet/IPv4 header
out of a `[u8]`. In C or Rust this is pointer casting; **in Sable it is
already safe code** — indexing plus arithmetic, with the representation
relation stated as a ghost function (exactly the utf8/varint/hex
corpus pattern, contracts and all). A zero-copy *typed view* of a byte
buffer is a lowering optimization, not an expressiveness gap. Unsafe
Sable does not need to exist for this example, which is worth saying
out loud: a chunk of what forces `unsafe` in Rust is reinterpretation,
and reinterpretation over value semantics is just math.

**5. Page tables and privileged state.** Write CR3, invalidate a TLB
entry, mask interrupts. Needs: effectful operations on machine state
outside the SVM, with ordering guarantees — same shape as MMIO
(effects, traces), plus §11's alternative-machine story: against a Sail
RISC-V model these become contracted intrinsics specified against
*that* model (the seL4 architecture with Sable in place of C).

**6. A spinlock.** Atomic compare-and-swap, fences, shared mutable
state between threads. Needs: a concurrent machine model. The SVM is
sequential; no boundary construct can paper over that. Named here so
its absence is a decision, not an oversight: concurrency is its own
machine-model extension (§12, rely-guarantee), and when it lands,
atomics will follow the same pattern as everything below — contracted
intrinsics with trace semantics — but the machine grows first.

## The observation: Rust's `unsafe` is three things wearing one keyword

1. **Trust** — axioms about the world: "this C function does what its
   man page says," "this address range is the UART."
2. **Model** — operations on state the type system does not govern:
   raw memory, device registers, privileged state.
3. **Evidence** — invariants the compiler cannot check, where the
   programmer knows more than the type system.

Rust discharges all three with the same keyword and a comment
convention. Sable already has (3), better: the §9 ladder — `defer` is
"check it at runtime," `assume` is a named, audited, tallied axiom, and
obligations are first-class objects. So the design problem for unsafe
Sable is (1) and (2) only. That reframing is most of this note's
content.

## Thesis: no `unsafe` keyword — a trusted boundary discipline

**Trust (1) becomes `extern` declarations with full contracts.** A
foreign function is declared with `pre`/`post` like any Sable function,
plus a mandatory audit payload (the `assume` precedent: a reason string
is not optional), plus an explicit frame clause. Call sites get the
posts as hypotheses and owe the pres as obligations — the machinery
that exists today for ordinary calls, unchanged. What is new is the
epistemic status: an extern contract is an *axiom about the world*,
counted and reported exactly like `assume`. The build report's ladder
gains one rung: `status: fully verified` versus `verified modulo N
boundary contracts`.

Because contracts are machine objects, the compiler can compute, for
every exported function, the transitive set of boundary axioms its
verification rests on — a **trust manifest**. This is the answer to
"where do I audit": not a grep for a keyword, but a computed, complete,
per-export list. (For a language where LLMs write most of the code,
the manifest is the artifact the human reviews.)

**Model (2) becomes machine growth with defined semantics.** Pillar 1
does not stop at the boundary — unsafe Sable code still has no UB,
because the machine model grows to give the new operations meaning:

- **Static regions.** `region UART0 at 0x10000000 size 0x100
  #[trust(reason := "SoC datasheet §...")]` declares a byte range as a
  statically-owned array. Disjointness of declared regions is part of
  the platform trust payload. A *RAM* region (DMA buffer, the heap
  before there is an allocator) then **is an owned `[u8]`** — indexing,
  stores, bounds VCs, ownership: all existing machinery, zero new
  verifier concepts. This is also exactly §11's `#[freestanding]`
  vocabulary ("statically declared regions").
- **Volatile regions and the event trace.** A device region's accesses
  are effects: the machine records each read/write as an event in a
  trace component of the configuration, and reads draw their values
  from an **input oracle** the machine is parameterized by. This is the
  `cap` move repeated (ADR 0005 res. 7): where "allocation may fail"
  threatened determinism, a capacity parameter restored it; where
  "device reads return anything" threatens it, an oracle parameter
  restores it, and soundness statements quantify over the oracle.
  Driver correctness becomes a trace predicate — example 1's "emits
  exactly this sequence" is a `post` about `trace`, device-independent
  and short.
- **Extern calls** are also trace events, and their effect on memory is
  havoc *bounded by the declared frame clause* — the same
  havoc-under-contract the verifier already performs at ordinary call
  sites for `&mut` arrays.
- **The failure receptacle already exists.** What happens when unsafe
  code is wrong? Nothing new: obligations that don't discharge are
  compile errors, and at the machine level the outcome of a
  statically-excluded state is `undef` (ADR 0005). The soundness
  statement survives verbatim — *verified programs never reach
  `undef`* — with a larger, explicitly enumerated axiom set. Unsafe
  Sable is not a second language; it is the same theorem with more
  hypotheses, all of them named.

**Monitorability comes along free-ish.** `sable test` runs boundary
code against a *scripted world*: stub implementations for externs,
scripts for the oracle, and the same dynamic contract checking as
everywhere else. Boundary contracts are exactly as testable as any
other contract — the sanitizer posture (§9) extends to the boundary,
which is more than "trust the comment" ever gave anyone.

## Staging (what the benchmarks force, in order)

- **v1 — extern + static regions + trace.** Enough for: FFI (example
  2, the adoption gate of §5), MMIO drivers (example 1), freestanding
  targets (§11), and privileged intrinsics as contracted externs
  (example 5, against the SVM; against Sail models later). Notably
  cheap: contracts, havoc-with-frames, and call machinery all exist;
  the machine grows a trace component and an oracle parameter — the
  same *kind* of extension the SVM has absorbed twice already (cap,
  frames), each time with agreement/determinism/progress re-proven.
- **v2 — permission carving (allocator-forced).** Splitting a region's
  ownership into disjoint sub-ranges; `assemble<T>` / `disassemble`
  primitives that convert between an owned byte range and a typed
  owned value under a stated representation relation. This is where
  separation-logic-shaped obligations genuinely enter; the design goal
  is to scope them to *these primitives only* — ordinary code, even
  allocator code around the carve points, stays in the value world.
  The arena allocator needs only monotone carving (never reuse) and is
  deliberately first; the free-list allocator adds permission return
  and reuse, and is the real exam. Start the formal side with
  address-set ghosts (`owns : set int` in contracts) and upgrade to a
  points-to assertion layer only if the free-list proofs strangle —
  the probe-first rule applies to logics too.
- **Non-goals here**: concurrency (own pillar, own machine extension);
  inline assembly beyond contracted intrinsics (the verified-lowering
  pillar owns that); alignment obligations (a lowering concern —
  regions are byte arrays in the model; noted as an open question for
  the native story).

## Open questions (taste, explicitly)

1. **Keyword or not.** This sketch says Sable needs no `unsafe` blocks:
   the searchlight for auditors is the trust manifest plus the
   `extern`/`region`/`assume` declarations, which are already visible,
   greppable syntax. The counterargument is familiarity — Rust
   engineers expect a block marker at the scene of the crime. If a
   marker is wanted, it should be *derived* (the compiler flags
   manifest-bearing functions in docs/hover) rather than written, so it
   cannot lie.
2. **Trust payload shape.** Reason string only (the `assume`
   precedent), or structured fields — ABI, layout, alignment,
   provenance — that tooling can act on?
3. **Oracle scripting in `sable test`.** Per-test-function scripts?
   A world-stub module convention? This decides how pleasant driver
   testing is, and deserves its own small design round with example 1
   implemented.
4. **How much of the trace is contract-visible.** Full event lists
   compose awkwardly; drivers may want trace *projections* ("the writes
   to UART0 are...") — ghost functions over the trace, probably, but
   unproven.

One adjacency worth recording: v2's carving wants to talk about
*places* — sub-parts of owned things with their own ownership — and so
does finishing first-class class values (§12: class-valued fields,
moves, `&mut` class borrows). Whichever lands first will dig the
foundation the other builds on.
