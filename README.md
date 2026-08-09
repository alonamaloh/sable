# Sable

Sable is an imperative, C-flavored language in which **every function carries a machine-checked proof of its contract**. One source file interleaves two languages: a C-like program language with no undefined behavior and an ownership-based memory model, and a Lean 4 proof language that lives entirely on lines beginning with `///`.

**Status: milestones M0–M6 (benchmarks) are complete.** Verified today: binary search, insertion sort, **quicksort and the merge kernel** (full `sorted ∧ permutation` specs with frame conditions), **hex and varint codecs** (pointwise specs plus kernel-checked round-trip theorems), classes with invariants (`BoundedStack`), and the escape-hatch assurance ladder — all in a corpus that doubles as the compiler's regression conscience. See [`docs/PLAN.md`](docs/PLAN.md) for milestone-by-milestone detail. The normative design documents (working draft 0.4):

- [`docs/design/sable-language-design.md`](docs/design/sable-language-design.md) — the language: syntax, contracts, ownership, ghost code, termination, escape hatches, the SVM machine model, and the staged trust story.
- [`docs/design/sable-goals-and-roadmap.md`](docs/design/sable-goals-and-roadmap.md) — the benchmark-driven roadmap, from verified sorting through a GMP-style bignum library to the kernel horizon.

## The idea in thirty seconds

```sable
/// pre  ∀ i j, 0 ≤ i → i < j → j < a.len → a.get i ≤ a.get j
/// post match result with
///      | some i => 0 ≤ i ∧ i < a.len ∧ a.get i = key
///      | none   => ∀ k, 0 ≤ k → k < a.len → a.get k ≠ key
fn binary_search(&[i32] a, i32 key) -> option<u64> {
    u64 lo = 0;
    u64 hi = a.len;
    /// invariant hi ≤ a.len
    /// invariant ∀ k, 0 ≤ k → k < lo → a.get k < key
    /// invariant ∀ k, hi ≤ k → k < a.len → key < a.get k
    /// variant   hi - lo
    while (lo < hi) {
        u64 m = lo + (hi - lo) / 2;
        if      (a[m] < key) { lo = m + 1; }
        else if (a[m] > key) { hi = m; }
        else                 { return some(m); }
    }
    return none;
}
```

This is not pseudocode: [`corpus/verifies/binary_search.sable`](corpus/verifies/binary_search.sable) verifies today — 19 obligations, 17 discharged automatically, 2 by short hand-written `discharge` scripts (the two that genuinely need the sortedness quantifier instantiated). Fold the `///` lines and it reads as plain C with a contract. The contract (`pre`/`post`) is **interface** — always shown, in docs, on hover. The loop annotations are **evidence** — dimmed, foldable, for the checker and the proof maintainer. A reader may ignore proofs; no reader may be shown a function without its contract.

## What works today

```sh
cd lean && lake build                    # once: build the Sable prelude
cd compiler && cargo build --release

sable check file.sable                   # verify: every obligation kernel-checked by Lean
sable test  file.sable                   # run test_* functions with dynamic contract checks
sable lsp                                # language server (stdio)
sable daemon                             # warm checker: ~0.25s/check instead of ~2.4s
```

- **The pipeline** (M0–M2): contracts, loops with invariants/variants, `for`/`range` sugar, arrays (`&[T]`, `&mut [T]` with stores and `old` state), `option`, recursion with measures, ghost definitions, `discharge NAME by <tactics>` for the obligations automation can't reach. Headline artifacts: **in-place insertion sort verified against the full `sorted ∧ permutation` spec**, binary search, gcd. The multiset library lives in [`lean/Sable/Perm.lean`](lean/Sable/Perm.lean), core-only.
- **The assurance ladder** (M3): `defer` (sound runtime trap) and `assume #[audit(reason := "...")]` (audited axiom), tallied in every build report; `status: fully verified` appears only at zero of both.
- **Dynamic checking** (M3): `sable test` executes tests with trap semantics and every monitorable contract — pres, posts, invariants, variant decrease — checked at runtime; the cheapest way to find a wrong spec is to run it.
- **Editor support** (M4): the LSP serves diagnostics (fast pass on every edit, full verification on save), contract-on-hover, folding, and semantic tokens that dim evidence lines. Setup for Neovim and VS Code in [`editors/`](editors/README.md).
- **Classes with invariants** (M5): `BoundedStack` from the design doc verifies with every obligation automatic — the class invariant is an obligation at init/`&mut`-method exits and an assumption at entries, checked dynamically too (including at RAII drop).
- **The Tier-0 benchmarks** (M6): quicksort (frame conditions across recursion), the merge kernel (count-based multiset spec), hex and varint codecs with kernel-checked round-trip theorems — plus the first slice of the SVM formalization ([`lean/Sable/SVM.lean`](lean/Sable/SVM.lean)) whose design-audit findings live in [`docs/notes/svm-draft.md`](docs/notes/svm-draft.md).

There is **no SMT solver in the trusted base**: routine obligations are closed by an automation portfolio inside Lean (`omega`, `grind`, `simp` — see [`lean/Sable/Auto.lean`](lean/Sable/Auto.lean)), and every proof, automated or hand-written, is checked by the Lean kernel. Division is Euclidean, matching Lean's `/` exactly (ADR 0004). The corpus (`corpus/`) is the compiler's conscience: programs that must verify, programs that must fail with a named diagnostic, dynamic tests that must pass with zero unmonitorable clauses, and dynamic tests that must be caught.

## Design pillars

1. **No undefined behavior.** Every program's meaning is defined by a formal machine model; anything that would be UB in C is either statically excluded by a proof obligation or has defined trap semantics.
2. **A formal machine model is the axiom base.** The Sable Virtual Machine, formalized in Lean, is the language's meaning — a semantic definition, not a runtime. The trusted base shrinks in explicit, honestly labeled stages (design §10.1); today's stage trusts the Rust VC generator and the Lean kernel, nothing else.
3. **Ownership before logic.** Rust-style unique ownership with borrowing, simplified. Because mutable aliasing is impossible in safe code, the verifier reasons about values, not heaps; framing is a type-system fact.
4. **Total verification, visible exceptions.** No build modes. An undischarged obligation is a compile error. The only ways past one are written in the source and tallied in every build: `defer` (sound runtime trap) and `assume` (audited axiom). Zero of both is *fully verified* — a property of code, not of build configuration.

Architecture in one sentence: the Rust compiler (`compiler/`) owns the program language, Lean owns the proof language, and verification is Lean-file generation — see [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) and the ADRs in [`docs/decisions/`](docs/decisions/).

## Where this is headed

The roadmap is benchmark-driven: each goal stresses one design axis, has a spec statable in a few lines, and has precedent in the verification literature bounding its effort. The spine: sorting and codecs → `Vec` and a hash map (forcing the generics design) → UTF-8 / JSON / DEFLATE / crypto kernels → a verified allocator (forcing the `unsafe` design) → the two pillars: a **GMP-style bignum library** verified to implement ℤ, and the **SVM interpreter written and verified in Sable itself**. The long-running horizon is a formally verified OS kernel; the metatheory track (mechanized soundness of the verifier) runs alongside once the language surface stabilizes.

## Provenance

The design and implementation are being developed in conversation with Claude (Anthropic). Everything here is subject to revision as real code generates friction — the design documents already carry corrections that the compiler forced (the doc's own `div_round_up` example had an overflow bug; the corpus keeps it as a must-fail).

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT), at your option. Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
