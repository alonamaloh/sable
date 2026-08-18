# Sable

[![CI](https://github.com/alonamaloh/sable/actions/workflows/ci.yml/badge.svg)](https://github.com/alonamaloh/sable/actions/workflows/ci.yml)

Sable is an imperative, C-flavored language in which **every function carries a
machine-checked proof of its contract**. One file interleaves two languages: a
C-like program language with no undefined behavior and an ownership-based
memory model, and a Lean 4 proof language living entirely on `///` lines.

```sable
/// pre  ∀ i j, 0 ≤ i → i < j → j < a.len → a.get i ≤ a.get j
/// post match result with
///      | some i => 0 ≤ i ∧ i < a.len ∧ a.get i = key
///      | none   => ∀ k, 0 ≤ k → k < a.len → a.get k ≠ key
fn binary_search(&[i32] a, i32 key) -> option<u64> {
    mut u64 lo = 0;
    mut u64 hi = a.len;
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

That is not pseudocode.
[`corpus/verifies/binary_search.sable`](corpus/verifies/binary_search.sable)
verifies today. Fold the `///` lines and it reads as plain C with a contract.

**A program that does not verify does not build.** Integers are exact — every
overflow, division, and index is an obligation rather than undefined behavior
or a silent wrap. There is no SMT solver: obligations are discharged by an
automation portfolio inside Lean, and every proof is checked by the Lean
kernel.

## Try it

```sh
cd compiler && cargo build --release

sable check file.sable          # verify — every obligation kernel-checked
sable test  file.sable          # run test_* functions with dynamic contract checks
sable daemon                    # optional warm checker, ~10x faster checks
```

**[Start with the tutorial →](docs/TUTORIAL.md)** — a short tour of the
language, whose examples are themselves verified by CI.

## Status

A research project, developed in the open, and further along than that usually
implies. Verified today: sorting (quicksort and the merge kernel with full
`sorted ∧ permutation` specs), binary search, hex/varint/UTF-8 codecs with
kernel-checked round-trip theorems, a JSON parser verified against the RFC 8259
grammar, a generic growable `Vec<T>`, a hash map verified against the
linear-probing contract, an in-band free-list allocator with mandatory client
leases, and the pillar: **arbitrary-precision `Nat` and signed `Integer` —
comparison, addition, subtraction, schoolbook multiplication, division, and
gcd, each verified against a one-line spec over its abstraction function**, and
lowered to native code.

Not there yet: broad backend coverage for aggregates, concurrency, floats
beyond range facts, and much of a standard library. See
[`docs/PLAN.md`](docs/PLAN.md) for the milestone-by-milestone record.

## Reading further

- [`docs/TUTORIAL.md`](docs/TUTORIAL.md) — the language in a dozen examples.
- [`corpus/`](corpus/) — the real documentation: ~120 programs that must
  verify, one program per diagnostic that must fail, and dynamic tests. CI
  keeps all of it green, so it never goes stale.
- [`docs/design/sable-language-design.md`](docs/design/sable-language-design.md)
  — the normative design: syntax, contracts, ownership, ghost code,
  termination, escape hatches, and the machine model.
- [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) — how the compiler works, and
  [`docs/decisions/`](docs/decisions/) for the reasoning behind each settled
  question.
