# ADR 0015 — String v1: a verified UTF-8 string as a library class

Date: 2026-08-10. Status: accepted, implemented. Concat/slicing/
codepoint iteration deferred (see Consequences).

## Context

Bare `"..."` literals were reserved by ADR 0014 for a `String` type.
The pieces to build one honestly all existed: class values with
invariants (ADR 0010), the kernel-verified utf8 module, modules to
import it (ADR 0013), operator bindings for comparison (ADR 0012),
and byte literals for test data. The forcing question was whether a
*literal* could construct a `String` without a hand-written proof at
every site.

## Decision

**`String` is a library class** (`corpus/verifies/string.sable`), not
a compiler builtin: owned `[u8] bytes` with class invariant
`validScan bytes 0`. The compiler's only knowledge of it is the
literal desugar (below).

- **`validScan`** (utf8 module) is the byte-table form of UTF-8
  validity — a forward scan over RFC 3629's lead/continuation ranges,
  no existential, so it lies in the monitorable fragment (the class
  invariant is checked dynamically at init exits and RAII drops) and
  reduces by rewriting on concrete bytes. It is tied to the canonical
  decomposability predicate by the kernel-checked
  `validScan_sound : validScan b pos → validFrom b pos`, so the
  invariant is not a second, unproven characterization of UTF-8.
- **Literal sites prove themselves.** The obligation at a literal is
  `validScan <concrete bytes> 0`. Ten *conditional step lemmas*
  (`validScan_ascii`, `validScan_two`, …) rewrite one scan step each,
  gated on byte-range side conditions; tagged for automation they
  unfold a literal's concrete bytes to `True` under plain `simp`,
  while an abstract `validScan` hypothesis (an invariant in scope)
  matches no lemma and is left untouched. Tagging the *recursive
  definition* itself was tried and rejected — simp descends the
  recursion under `ite` congruence on abstract arguments and blows
  the recursion limit.
- **`#[unfold]`** is the general mechanism this forced: a ghost `def`
  or `theorem` marked `#[unfold]` is emitted `@[simp]`, opting into
  the automation simp set. (Default policy unchanged: non-recursive
  defs are tagged, recursive ones are not.)
- **`var s = "Hi!";` is parser sugar** for a hidden `[u8]` temp
  holding the literal's UTF-8 bytes plus
  `String::from_bytes(&temp)` — the one lang-item-by-name coupling:
  the parser names `String::from_bytes`; the library defines its
  meaning. The lexer guarantees bare literals are valid UTF-8
  (`lex.string_not_utf8` — escapes could smuggle arbitrary bytes;
  those belong in `b"..."`), so the generated pre always discharges.
  v1 restriction: bare literals appear only as `var` initializers
  (`string.literal_position` elsewhere).
- **Array-literal locals** now exist in verified functions (they were
  test-only): vcgen binds a fresh `Seq` with concrete length and
  per-element facts — which is exactly what makes the literal's
  validity obligation concrete.
- **Comparison**: `cmp` is byte-lexicographic under the −1/0/1
  convention with a full iff contract (first-difference witness for
  `-1`, byte-equality for `0`, range), bound through `operator cmp`,
  so all six comparison operators work on `String`. For valid UTF-8,
  byte order is codepoint order and byte equality is codepoint
  equality — the encoding is order-preserving and injective.

## Consequences

- The copy in `from_bytes` needs `validScan_congr` (validity respects
  byte-for-byte agreement on the in-range prefix — `Seq.get` is junk
  off-range, so sequences are never propositionally equal and a
  congruence lemma, not extensionality, is the right tool).
- Deferred: `concat` (needs a validScan-append lemma and buffer
  building), slicing (byte offsets can split a character — the design
  landmine, deliberately unbanked), codepoint iteration (wants the
  decoder as a method), `String` in assignment/argument positions for
  bare literals.
- The monitor evaluates `validScan` per invariant check in exact
  arithmetic; strings in dynamic tests stay short by the same
  envelope discipline as bignum's limbs.
