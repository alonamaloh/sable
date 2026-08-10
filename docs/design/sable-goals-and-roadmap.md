# Sable — Goals and Roadmap

*Companion to the language design document. Subject to revision as experience accumulates.*

## What makes a good goal for this project

Each goal should satisfy three criteria:

1. **It stresses a specific design axis** of the language — a benchmark should tell us whether a particular design decision (the `///` two-tier split, `defer` ergonomics, ownership, totality-by-default) survives contact with real code.
2. **Its specification is short.** A spec statable in a few lines means the benchmark measures the proof pipeline, not requirements archaeology.
3. **It has precedent** in the verification literature, so we know it is a bounded effort (PhD-scale or less), not open research.

Goals below are grouped in tiers. Within tiers, sequencing notes say what each goal produces that later goals consume.

---

## Tier 0 — Warm-ups: ergonomics and the lemma library

**Sorting suite** (insertion, merge, quicksort/introsort).
Spec: `sorted(result) ∧ multiset(result) = multiset(old a)`. The permutation half is the classic beginner trap and immediately tests whether the ghost `seq`/multiset library is pleasant to use. These are also the tutorial chapters; the language lives or dies on whether chapter 3 of the book is convincing.

**Round-trip codecs** (Base64, hex, varint/LEB128).
Spec: `decode(encode x) = some x`, `encode` injective. One-line total-correctness specs exercising `option`, byte slices, and bit manipulation.

*Produces*: the ghost-sequence lemma library that the bignum addition invariant and everything else consumes.

## Tier 1 — Standard library: what everything rests on

**Growable `Vec<T>` and a hash map.**
Model-based specification style: `ghost model : seq T` / `map K V`, every method contracted against the model. Forces two designs the core language defers:

- Generics with **law-carrying trait bounds** (`T: Hashable` where `hash` must respect equality — the first contracted interface).
- Amortized-capacity invariants, if complexity claims are wanted beyond functional correctness.

Precedent: Verus. Known-hard-but-tractable; deliberately scheduled early so benchmark pressure, not speculation, drives the generics design. One boundary on that: the benchmark drives the *surface* design (trait syntax, law-carrying bounds, contract inheritance), not the compilation strategy — monomorphization before VC generation is committed upfront (design §12), so the VCgen and the eventual metatheory never see type variables. Retrofitting that decision later is famously painful; it is not left to benchmark pressure.

## Tier 2 — Breadth: one benchmark per design axis

**UTF-8 decoder** — *the external-standard axis.* The spec is transcribed from someone else's prose (Unicode's well-formedness tables) into ghost definitions a reader can check against the standard by eye; the branchy, table-driven decoder is then proven equivalent. Tests whether interface blocks carry real documentation weight. Independently useful: malformed-UTF-8 handling is a perennial CVE source.

**JSON (or TOML) parser** — *the inductive-grammar axis.* Ghost inductive `Json`, ghost relation `represents : seq u8 → Json → Prop`; theorems: parser accepts *iff* the relation holds (soundness + completeness), and `parse ∘ print = some`. Stresses recursion with variant measures on input position and will reveal whether `partial` leaks annoyingly into recursive descent. Precedent: EverParse (deployed in Azure) — and its famously unreadable specs make a flattering comparison target.

**DEFLATE decompressor** — *the bit-level-state axis.* Huffman tables, sliding windows, bit readers spanning byte boundaries. The benchmark for whether loop invariants over intricate mutable state stay in the evidence layer or strangle the program text. Spec: output is a valid decompression per RFC 1951. Precedent: a verified Coq implementation exists and documented its pain level; beating that pain level is a headline result.

**ChaCha20 + SHA-256 against the RFCs** — *the total-arithmetic axis.* Nearly all `wrap()` arithmetic by intent: no overflow VCs, pure functional correctness against transcribed RFC pseudocode. Precedent: HACL*, Fiat-Crypto. Also the prototyping ground for a future `secret` type qualifier whose obligations forbid branching or indexing on secret data — constant-time as a proof obligation. (Elliptic curves scoped out initially; Fiat-Crypto shows field arithmetic is really a compilation problem.)

**Arena allocator, then free-list allocator** — *the unsafe-boundary axis.* Allocators cannot live in safe Sable: their job is manufacturing ownership from raw bytes. The real deliverable is the **design of unsafe Sable** — how small the `unsafe` region can be, what separation-logic obligations the boundary demands, whether the proof stays in the evidence layer. Precedent: verified allocators in Verus. Kernel-track work (Tier 4) consumes these answers — and so does any adoption story: FFI rides on the same boundary design, and until it lands, Sable is a research artifact, not a usable language (design §5). This benchmark is therefore the gate on the project's first adoption claim, not just a kernel prerequisite.

## Tier 3 — Moonshot: the bignum library

**A GMP-style arbitrary-precision integer library, verified to implement the unrestricted integers, up to running out of memory.**

Why this is the crown-jewel *library* target:

- **The spec-to-code ratio is perfect.** The entire specification is one abstraction function and one line per operation:

  ```sable
  /// def value (l : seq u64) : nat :=           -- little-endian, base B = 2^64
  ///   if l.len = 0 then 0 else (l.get 0 : nat) + B * value l.tail

  /// post value result.limbs = value a.limbs * value b.limbs
  fn mul(&Nat a, &Nat b) -> Nat { ... }
  ```

  "Implements the integers" is fully captured by `value` being a homomorphism into ℤ. No I/O, no fuzzy requirements: the proof is the whole game, which is what you want when the thing under test is the proof pipeline.

- **Calibrated difficulty.** WhyMP (Rieu-Helft, Marché, Melquiond; Inria) verified a GMP-compatible mpn layer in Why3 — through divide-and-conquer multiplication, Knuth long division, square root — at roughly one PhD of effort and ~20k proof lines for ~5k code lines, with performance competitive with GMP's generic-C build. Sable's claim: same artifact, substantially cheaper and vastly more readable, because ownership plus the two-tier `///` design eliminates most of the annotation burden.

- **It exercises every hard part on purpose.** Addition's carry invariant is SMT-automatic (validates the pleasant path). Multiplication needs nonlinear `Σᵢ aᵢBⁱ` rearrangement lemmas where SMT dies — exactly what the evidence layer and `discharge` exist for. Division needs Knuth's q̂-bound (estimate exceeds true digit by ≤ 2), a genuinely subtle pen-and-paper lemma. "Up to OOM" is formalized by the named-trap semantics: *every execution either satisfies the contract or halts in the OOM trap.* GMP-style operand aliasing becomes a non-issue: illegal aliasing patterns are type errors, in-place operations are `&mut self` methods.

**Milestones** (stealing WhyMP's hindsight):

1. `Nat` with normalization invariant (no leading zero limb ⇒ `value` injective ⇒ equality is limb equality); `cmp`, `add`, `sub` (with `pre a ≥ b` on magnitude subtraction). All obligations SMT-automatic — validates the whole pipeline end to end.
2. Schoolbook `mul`; division by a single limb. First real Lean lemmas.
3. Knuth Algorithm D long division — the boss fight. When `/// theorem qhat_bound` is discharged, the moonshot is essentially won. *(Done, 2026-08-10: `div` is Algorithm D, `qhat_ge`/`qhat_le4` discharged and load-bearing for the counted correction loop; quarter-normalization deviation recorded in `docs/notes/algd-probe.lean`. See PLAN.md M24.)*
4. Signed `Int` wrapper (sign + magnitude; pure algebra over `Nat`, almost free); GMP-shaped public API.
5. Karatsuba, introduced with its recombination proof `defer`red, benchmarked, then defers ratcheted to zero — the intended workout for the §9 escape-hatch design.

**Honest scope note**: verified code can match GMP's *generic-C* build; GMP's hand-written assembly kernels remain 2–4× faster, and matching them requires verified intrinsic lowering (`carrying_add` → `adc`). "Provably implements ℤ, within 2× of GMP" is already a result nobody has in a language this readable.

## Tier 3′ — Dogfood moonshot: the SVM interpreter, in Sable

Write the SVM as a Sable program and prove it implements the inductive step relation from the design document — the CakeML move, scoped down to an interpreter (very achievable) rather than a verified compiler (decade-scale, deferred).

Payoff: the language's own semantics becomes a program in the language; the Lean formalization becomes executably testable; and every future "does the compiler match the SVM?" question gains a differential-testing oracle for free. Bignum proves the language can verify *other* things; this proves it can verify *itself*. Together they make the project undeniable.

It is also the load-bearing artifact of the stage-1 trust posture (design §10.1): while the VC generator is still trusted engineering, this interpreter plus the Lean formalization is what cross-checks it.

## Tier 3″ — Metatheory track: mechanizing soundness

**Stage 2 of the trusted-base ladder (design §10.1): a mechanized proof that the VC generator is sound against the SVM step relation** — VCgen correctness, ghost-erasure soundness, and the ownership-implies-frame-rule metatheorem. This retires the VCgen from the trusted base, leaving the machine formalization and the Lean kernel.

This is scheduled as its own tier — not folded into the design pillars — because it is the one item on this roadmap that is *not* PhD-scale-with-precedent in the comfortable sense the other tiers are. The nearest precedent, RustBelt, took a team at MPI-SWS years for a fragment of Rust. Three things keep it tractable here, and they are design decisions, not hopes: the language surface is deliberately small (lexical borrows, no closures, no lifetimes, no concurrency); monomorphization means the metatheory never sees type variables; and the SVM is a boring ~40-rule stack machine rather than a real ISA.

Sequencing: it sits on the critical path of nothing in Tiers 0–3. It starts only after the language surface stabilizes (post-stdlib tier — mechanizing a moving target is wasted work), runs long, and its first standalone publishable artifact is the frame-rule metatheorem for the ownership discipline alone. Until it completes, every verification claim is honestly labeled stage 1: "verified, modulo trusted VCgen, differentially tested against the formal semantics."

## Tier 4 — The kernel direction

**Crown jewel: a formally verified OS kernel.** The apparent objection — "a VM language can't write a kernel" — dissolves on inspection: the SVM is a semantic definition, not a runtime, and the architecture of the field's flagship results is exactly "source proven against a formal model, refined down to metal" (seL4: C against Isabelle; CakeML: formal semantics compiled by verified translation to bare ARM/x64). A Sable kernel would never execute SVM steps, any more than seL4 executes Isabelle.

Four workstreams close the gap, each with standalone artifacts:

1. **Freestanding profile** (now in design §11): no allocator, static regions, user-supplied panic handler. Cheap to specify; independently serves embedded firmware; shrinks the trusted base.
2. **Machine model swap**: adopt an off-the-shelf mechanized ISA (Sail RISC-V is the leading candidate for its small formal surface; ARM's machine-readable spec is the alternative) plus MMU and privilege model as the layer below the language. Privileged operations become contracted `unsafe` intrinsics specified against that model.
3. **Translation validation**: per-build proof that *this* binary refines *this* program — how seL4 closed its binary gap; dramatically cheaper than a verified compiler and the critical-path item for any bare-metal claim. A full CompCert/CakeML-style verified backend is a later pillar.
4. **Interrupt discipline**: adopt seL4's design dodge — a mostly-atomic event-loop kernel with explicit preemption points, so verified code is sequential between yields — postponing rely-guarantee concurrency to the multicore future.

**Why Sable is unusually well-positioned**: most of seL4's ~20 person-years went into hand-proving invariants (no aliasing between subsystems, no use-after-free of kernel objects, initialization) that Sable's type system gives *by construction*; ownership-based verified-OS efforts (VeriSMo, Atmosphere, verified NrOS components) report order-of-magnitude cheaper proofs for exactly this reason. Deeper still: Hyperkernel and Serval achieved push-button SMT kernel verification by imposing a *finite interface* discipline — every syscall terminating with bounded loops. That discipline is Sable's default semantics: a kernel whose syscalls are ordinary (non-`partial`) functions is a Hyperkernel-style kernel by construction, with only the top-level event loop marked `partial`.

**Ladder**: freestanding profile → allocator benchmark (feeds unsafe design) → Sail RISC-V machine layer + verified page-table library (standalone publishable; memory management is where kernel bugs live) → first bare-metal firmware image (Komodo-scale) → separation kernel / unikernel with finite syscall interface (a real security artifact well short of POSIX) → the crown jewel.

## Explicitly excluded, for now

- **Crash-safe storage** (FSCQ-style): doable but the crash-recovery proof machinery is research-scale infrastructure; premature.
- **Concurrency benchmarks**: blocked on the rely-guarantee design. When it lands, the first benchmark is an SPSC ring buffer — not before.
- **Floating-point error-bound verification**: open-ended; range/NaN facts only.
- **Verified compiler backend**: a decade-scale pillar; translation validation covers the near term.

## Sequencing summary

```
sorts → Vec → bignum (complete through gcd)    ← done; each fed the next
      ↘ hash map (forces generics design)
codecs → UTF-8 → JSON parser → DEFLATE          ← breadth track, parallelizable
crypto kernels (ChaCha20/SHA-256)               ← independent; prototypes `secret`
arena → free-list allocator                     ← unsafe-Sable design track
bignum M2–M5                                    ← moonshot completion
SVM interpreter in Sable                        ← after stdlib tier is stable
frame-rule metatheorem → mechanized VCgen soundness
                                                ← metatheory track, starts after
                                                  surface stabilizes; long-running
freestanding → Sail RISC-V layer → page tables → firmware → separation kernel
                                                ← kernel track, long-running
```

The two pillars are **bignum** (the language can verify other things) and the **self-hosted SVM interpreter** (the language can verify itself). The standard-library tier is what everything rests on; the breadth tier is the demonstration that each domain gets a different answer to "why should I care"; the metatheory track is what upgrades every claim from stage 1 to stage 2 trust (design §10.1); the kernel track is the horizon.
