# Sable

[![CI](https://github.com/alonamaloh/sable/actions/workflows/ci.yml/badge.svg)](https://github.com/alonamaloh/sable/actions/workflows/ci.yml)

Sable is an imperative, C-flavored language in which **every function carries a machine-checked proof of its contract**. One source file interleaves two languages: a C-like program language with no undefined behavior and an ownership-based memory model, and a Lean 4 proof language that lives entirely on lines beginning with `///`.

**Status: milestones M0–M41 are complete.** Verified today: binary search, insertion sort, **quicksort and the merge kernel** (full `sorted ∧ permutation` specs with frame conditions), **hex and varint codecs** (pointwise specs plus kernel-checked round-trip theorems), classes with invariants (`BoundedStack`), a **generic growable `Vec<T>`** with its reallocation frame condition, a **hash map verified against the linear-probing contract** under a law-carrying `Hashable` trait bound, a **UTF-8 codec with a kernel-checked roundtrip**, a **JSON parser verified against the recursive RFC 8259 grammar** (tokenizer + structural validation), C++-`optional`-style **option accessors** whose syntax works identically in code and contracts, **the bignum pillar — arbitrary-precision `Nat` with cmp/add/sub, schoolbook multiplication, division, and gcd, every operation verified against a one-line spec over the abstraction function** (now written with operators: `q = q + m` under `while (r >= b)`), a **verified UTF-8 `String` with self-proving literals**, file-based **modules**, the escape-hatch assurance ladder, and a **verified in-band free-list allocator with mandatory client leases, first-fit allocation, exact return, and proved local coalescing** — all in a corpus that doubles as the compiler's regression conscience. See [`docs/PLAN.md`](docs/PLAN.md) for milestone-by-milestone detail. The normative design documents (working draft 0.4):

- [`docs/design/sable-language-design.md`](docs/design/sable-language-design.md) — the language: syntax, contracts, ownership, ghost code, termination, escape hatches, the SVM machine model, and the staged trust story.
- [`docs/design/sable-goals-and-roadmap.md`](docs/design/sable-goals-and-roadmap.md) — the benchmark-driven roadmap, from verified sorting through a GMP-style bignum library to the kernel horizon.

## The idea in thirty seconds

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

This is not pseudocode: [`corpus/verifies/binary_search.sable`](corpus/verifies/binary_search.sable) verifies today — 19 obligations, 17 discharged automatically, 2 by short hand-written `discharge` scripts (the two that genuinely need the sortedness quantifier instantiated). Fold the `///` lines and it reads as plain C with a contract. The contract (`pre`/`post`) is **interface** — always shown, in docs, on hover. The loop annotations are **evidence** — dimmed, foldable, for the checker and the proof maintainer. A reader may ignore proofs; no reader may be shown a function without its contract.

## What works today

```sh
cd lean && lake build                    # once: build the Sable prelude
cd compiler && cargo build --release

sable check file.sable                   # verify: every obligation kernel-checked by Lean
sable test  file.sable                   # run test_* functions with dynamic contract checks
sable check -M lib/ app.sable            # resolve `use` imports against lib/ (ADR 0013)
sable lsp                                # language server (stdio)
sable daemon                             # warm checker: ~0.25s/check instead of ~2.4s
```

- **The bignum pillar** (M15–M16, the Tier-3 opener): arbitrary-precision `Nat` over base-2³² limbs with a normalizing representation invariant ([`corpus/verifies/bignum.sable`](corpus/verifies/bignum.sable)). The entire specification is one recursive ghost valuation, `natVal`, and one line per operation: `cmp` decides the order, `add`/`sub`/`mul` post `natVal result.limbs = natVal a.limbs ⊕ natVal b.limbs`, `div`/`rem` post `… = natVal a.limbs / natVal b.limbs` against Lean's own Euclidean division — with division built *compositionally* (double-and-subtract riding the contracts of the other verified ops, closed by one uniqueness lemma) — and `gcd` is Euclid in fifteen lines whose spec is kernel-check-proven to agree with Lean core's `Int.gcd`. **255 obligations across 10 functions, 73 hand discharges, zero escapes**, every clause monitored dynamically — the first benchmark where the mathematics itself was the test.
- **The verified free-list allocator** (M41, ADR 0037–0052): releasable system roots fold into an affine aggregate; first-fit allocation returns an exact mandatory `BlockLease`; public return rejects the wrong allocator, repeated use, or substituted subregion metadata; and predecessor/successor coalescing clears real in-band headers and proves exact span joins ([`corpus/verifies/free_list_return.sable`](corpus/verifies/free_list_return.sable)). Six branch fixtures and a deterministic 144-return reference-model comparison exercise the runtime policy, while final destruction still requires the exact complete root authority.
- **The pipeline** (M0–M2): contracts, loops with invariants/variants, `for`/`range` sugar, arrays (`&[T]`, `&mut [T]` with stores and `old` state), `option`, recursion with measures, ghost definitions, `discharge NAME by <tactics>` for the obligations automation can't reach, and inline `/// assert` stepping-stones that turn one proved fact into a hypothesis for everything downstream. Headline artifacts: **in-place insertion sort verified against the full `sorted ∧ permutation` spec**, binary search, gcd. The multiset library lives in [`lean/Sable/Perm.lean`](lean/Sable/Perm.lean), core-only.
- **The assurance ladder** (M3): `defer` (sound runtime trap) and `assume #[audit(reason := "...")]` (audited axiom), tallied in every build report; `status: fully verified` appears only at zero of both.
- **Dynamic checking** (M3): `sable test` executes tests with trap semantics and every monitorable contract — pres, posts, invariants, variant decrease — checked at runtime; the cheapest way to find a wrong spec is to run it.
- **Editor support** (M4): the LSP serves diagnostics (fast pass on every edit, full verification on save), contract-on-hover, folding, and semantic tokens that dim evidence lines. Setup for Neovim and VS Code in [`editors/`](editors/README.md).
- **Classes with invariants** (M5): `BoundedStack` from the design doc verifies with every obligation automatic — the class invariant is an obligation at init/`&mut`-method exits and an assumption at entries, checked dynamically too (including at RAII drop).
- **The Tier-0 benchmarks** (M6): quicksort (frame conditions across recursion), the merge kernel (count-based multiset spec), hex and varint codecs with kernel-checked round-trip theorems — plus the first slice of the SVM formalization ([`lean/Sable/SVM.lean`](lean/Sable/SVM.lean)) whose design-audit findings live in [`docs/notes/svm-draft.md`](docs/notes/svm-draft.md).
- **Generics v1 and `Vec<T>`** (M7): explicit instantiation over the integer types, expanded by monomorphization before any verification stage runs (ADR 0006). Headline artifact: a growable **`Vec<T>` with amortized-doubling `push` verified with its full frame condition across the reallocation-and-copy path** ([`corpus/verifies/vec.sable`](corpus/verifies/vec.sable)) — the capacity invariant makes doubling overflow-free by construction, and the frame posts are also *monitored* at runtime, not just proven.
- **The UTF-8 codec** (M9, Tier 2 opener): RFC 3629 encoder + validating decoder (overlongs, surrogates, the 0x10FFFF ceiling) with a **kernel-checked roundtrip** and **buffer-level validation proven against a recursive decomposability predicate** ([`corpus/verifies/utf8.sable`](corpus/verifies/utf8.sable)) — 205 obligations, 7 hand discharges; the decoder provably never rejects canonical bytes.
- **`const` + immutability** (M22, ADR 0016): named compile-time constants usable in contracts (`pre b.len ≤ MAX_BYTES`), and **locals are immutable unless declared `mut`** — assignment, stores, `&mut` borrows, and `&mut` methods all require the marker, so every unmarked local is a proven-constant read.
- **String v1** (M21, ADR 0015): `var s = "héllo";` — a verified UTF-8 string as a *library class*, not a builtin: owned bytes under a monitorable validity invariant (`validScan`, kernel-tied to the RFC 3629 decomposability predicate), literals whose validity obligations **discharge automatically** (conditional step lemmas unfold concrete bytes under plain simp), and byte-lexicographic comparison with full iff contracts bound through `operator cmp`.
- **Byte-string literals** (M20, ADR 0014): `b"{\"key\": true}"` is a `[u8]` literal of its UTF-8 bytes (escapes `\n \r \t \0 \\ \" \xNN`; raw non-ASCII text contributes its UTF-8 bytes), replacing the decimal byte arrays the codec tests used to carry. Bare `"..."` is reserved for the future `String` type so no literal ever changes meaning.
- **Modules v1** (M19, ADR 0013): `use bignum;` — file-based, Rust-flavored imports (module = file, resolved against the importing file's directory then `-M` paths), transitive and cycle-checked, with diagnostics that always point into the *right* file. Linking is source-level, so every stage below the loader is module-oblivious; the dynamic-test corpus now imports its subjects instead of carrying 700-line copies.
- **Operator bindings** (M18, ADR 0012): `operator + = add;` binds operators to contracted functions — bignum arithmetic reads `q = q + m; r = r - d;` under `while (r >= b)`, and every operator use carries the bound function's full contract (the program `+` and the proof `+` never meet, so the sugar is purely front-end).
- **First-class class values** (M14, ADR 0010): shared class borrows, class returns, field reads, and (forced by division) class-local reassignment with move-in semantics — `fn union_of(&Range a, &Range b) -> Range` verifies with contracts written directly over class structures (`result.lo ≤ a.lo`), borrowed arguments carrying their invariants in and returned values carrying them out as checked obligations. The bignum surface, delivered exactly when the pillar demanded it.
- **Concepts** (M13, ADR 0009): type preconditions on templates — `/// requires T.max ≥ 100` — with **every generic declaration — functions, classes, trait-bounded templates — verified once against an abstract type model** (trait bounds become abstract spec-function binders) and instantiations owing only the (automatic) precondition facts: `HashMap`'s 27 per-instance discharges are one template set. C++ concepts check syntax; Sable concepts check lemmas. Plus `#[label(name)]`: stable semantic names for obligations and their hypotheses.
- **The JSON parser** (M12): structural validation against the full recursive value grammar ([`corpus/verifies/json_parse.sable`](corpus/verifies/json_parse.sable)) — the grammar is one mode-encoded well-founded ghost predicate with guarded recursion, the parser one self-recursive function with interior loops, and `json_valid` returning true is a kernel-checked proof the buffer is a JSON value: 270 obligations, the largest verified artifact in the corpus.
- **Option accessors** (M11, ADR 0008): `option<T>` locals with `.is_some`/`.value` — no pattern matching in the program language, as a standing principle. `.value` carries a someness obligation (junk-on-none in the model, exactly like `Seq.get` off-range; a trap in `sable test`), and the prelude makes the identical postfix syntax elaborate in clause text: `post result.is_some → result.value = x + 1`.
- **The JSON tokenizer** (M10): the RFC 8259 lexical grammar as ghost predicates — recursive string bodies with variable-width escapes, ∃-split numbers, a guarded-recursion token-stream predicate — with scanners proven against them ([`corpus/verifies/json_lex.sable`](corpus/verifies/json_lex.sable)): 175 obligations, 11 discharges; `json_lex_ok` returning true is a kernel-checked proof the buffer tokenizes.
- **Traits v1 and the hash map** (M8): law-carrying bounds (ADR 0007) — a trait pairs a spec-level function with a program method contracted to compute it, so generic specs can *apply* `K::hash` and get determinism; impls are verified against the law, not trusted. Headline artifact: **`HashMap<K: Hashable, V>` with open addressing verified against the linear-probing contract** ([`corpus/verifies/hashmap.sable`](corpus/verifies/hashmap.sable)) — `get` returning `none` *proves* the key is absent from the whole table, cyclic probing stays in omega's fragment by subtraction instead of variable modulus, and every clause (including the probe-path invariant and existential posts) is monitored dynamically at zero skips.

There is **no SMT solver in the trusted base**: routine obligations are closed by an automation portfolio inside Lean (`omega`, `simp`, and a heartbeat-budgeted `grind` whose expensive successes produce a warning with a minimized-proof suggestion, ADR 0011 — see [`lean/Sable/Auto.lean`](lean/Sable/Auto.lean)), and every proof, automated or hand-written, is checked by the Lean kernel. Division is Euclidean, matching Lean's `/` exactly (ADR 0004). The corpus (`corpus/`) is the compiler's conscience: programs that must verify, programs that must fail with a named diagnostic, dynamic tests that must pass with zero unmonitorable clauses, and dynamic tests that must be caught.

## Design pillars

1. **No undefined behavior.** Every program's meaning is defined by a formal machine model; anything that would be UB in C is either statically excluded by a proof obligation or has defined trap semantics.
2. **A formal machine model is the axiom base.** The Sable Virtual Machine, formalized in Lean, is the language's meaning — a semantic definition, not a runtime. The trusted base shrinks in explicit, honestly labeled stages (design §10.1); today's stage trusts the Rust VC generator and the Lean kernel, nothing else.
3. **Ownership before logic.** Rust-style unique ownership with borrowing, simplified. Because mutable aliasing is impossible in safe code, the verifier reasons about values, not heaps; framing is a type-system fact.
4. **Total verification, visible exceptions.** No build modes. An undischarged obligation is a compile error. The only ways past one are written in the source and tallied in every build: `defer` (sound runtime trap) and `assume` (audited axiom). Zero of both is *fully verified* — a property of code, not of build configuration.

Architecture in one sentence: the Rust compiler (`compiler/`) owns the program language, Lean owns the proof language, and verification is Lean-file generation — see [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) and the ADRs in [`docs/decisions/`](docs/decisions/).

## Where this is headed

The roadmap is benchmark-driven: each goal stresses one design axis, has a spec statable in a few lines, and has precedent in the verification literature bounding its effort. The spine: sorting and codecs → `Vec` and a hash map (forcing the generics design) → UTF-8 / JSON / DEFLATE / crypto kernels → a verified allocator (forcing the `unsafe` design) → the two pillars: a **GMP-style bignum library** verified to implement ℤ (its core arithmetic — through multiplication and division — is done), and the **SVM interpreter written and verified in Sable itself**. The long-running horizon is a formally verified OS kernel; the metatheory track (mechanized soundness of the verifier) runs alongside once the language surface stabilizes.

## Provenance

The design and implementation are being developed in conversation with Claude (Anthropic). Everything here is subject to revision as real code generates friction — the design documents already carry corrections that the compiler forced (the doc's own `div_round_up` example had an overflow bug; the corpus keeps it as a must-fail).

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or [MIT license](LICENSE-MIT), at your option. Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in this work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions.
