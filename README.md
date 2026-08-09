# Sable

Sable is a design for an imperative, C-flavored language in which **every function carries a machine-checked proof of its contract**. One source file interleaves two languages: a C-like program language with no undefined behavior and an ownership-based memory model, and a Lean 4–dialect proof language that lives entirely on lines beginning with `///`.

**Status: early implementation — milestone M0 (the full verify pipeline, straight-line programs) is complete; next is M1: loops, arrays, `option`, `discharge`. See [`docs/PLAN.md`](docs/PLAN.md).** The normative design documents (working draft 0.4):

- [`docs/design/sable-language-design.md`](docs/design/sable-language-design.md) — the language: syntax, contracts, ownership, ghost code, termination, escape hatches, the SVM machine model, and the staged trust story.
- [`docs/design/sable-goals-and-roadmap.md`](docs/design/sable-goals-and-roadmap.md) — the benchmark-driven roadmap, from verified sorting through a GMP-style bignum library to the kernel horizon.

The compiler is written in Rust (`compiler/`); the proof language is checked by Lean itself against the prelude in `lean/` — see [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) and the ADRs in [`docs/decisions/`](docs/decisions/).

## The idea in thirty seconds

```sable
/// pre  a.len ≤ 2^32
/// post result = spec_sum a 0 a.len
fn sum(&[i32] a) -> i64 {
    i64 acc = 0;
    u64 i = 0;
    /// invariant i ≤ a.len
    /// invariant acc = spec_sum a 0 i
    /// invariant acc.abs ≤ i * i32.max      -- why the addition below can't overflow
    /// variant   a.len - i
    while (i < a.len) {
        acc = acc + widen<i64>(a[i]);
        i = i + 1;
    }
    return acc;
}
```

Fold the `///` lines and this reads as plain C with a two-line contract. The contract (`pre`/`post`) is **interface** — always shown, in docs, on hover. The loop annotations are **evidence** — dimmed, foldable, for the checker and the proof maintainer. A reader may ignore proofs; no reader may be shown a function without its contract.

## Design pillars

1. **No undefined behavior.** Every program's meaning is defined by a formal machine model; anything that would be UB in C is either statically excluded by a proof obligation or has defined trap semantics.
2. **A formal machine model is the axiom base.** The Sable Virtual Machine, formalized in Lean, is the language's meaning — a semantic definition, not a runtime. The trusted base shrinks in explicit, honestly labeled stages.
3. **Ownership before logic.** Rust-style unique ownership with borrowing, simplified. Because mutable aliasing is impossible in safe code, the verifier reasons about values, not heaps; framing is a type-system fact.
4. **Total verification, visible exceptions.** No build modes. An undischarged obligation is a compile error. The only ways past one are written in the source and tallied in every build: `defer` (sound runtime trap) and `assume` (audited axiom). Zero of both is *fully verified* — a property of code, not of build configuration.

Functions are total by default; `partial` is an honest, documented label. Verification runs through SMT for the routine obligations, with a named-obligation `discharge ... by <tactic>` escape into Lean for the hard ones.

## Where this is headed

The roadmap is benchmark-driven: each goal stresses one design axis, has a spec statable in a few lines, and has precedent in the verification literature bounding its effort. The spine: sorting and codecs → `Vec` and a hash map (forcing the generics design) → UTF-8 / JSON / DEFLATE / crypto kernels → a verified allocator (forcing the `unsafe` design) → the two pillars: a **GMP-style bignum library** verified to implement ℤ, and the **SVM interpreter written and verified in Sable itself**. The long-running horizon is a formally verified OS kernel; the metatheory track (mechanized soundness of the verifier) runs alongside once the language surface stabilizes.

## Provenance

The design documents were developed in conversation with Claude (Anthropic). Everything here is subject to revision as real code generates friction.
