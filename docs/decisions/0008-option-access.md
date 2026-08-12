# ADR 0008 — Option consumption: accessors, not pattern matching

Date: 2026-08-09. Status: accepted.

## Context

Since M1, `option<T>` was return-position-only: a caller could forward
an option or drop it, nothing else. Tier 2 worked around the gap with
positional sentinels (`utf8_step`/`json_token` return 0-or-end), which
dies the moment the payload is an arbitrary value — `HashMap::get`
returning `option<V>` has no out-of-band bit pattern left. The JSON
parser forces the design.

A `match` statement was considered and **rejected on principle**: the
program language is C-flavored by conviction, and pattern-matching
syntax is exactly what Sable's author is building away from — to the
point of contemplating replacing Lean as the proof language for
readability. **Pattern matching does not enter the program language.**
This is a standing design principle, not a v1 scope cut.

## Decision

C++ `std::optional` style, field-postfix like `.len`:

- **Option-typed locals**: `option<u32> r = decode_utf8(&b, pos);`
- **`r.is_some`** — `bool`: does the option hold a value.
- **`r.value`** — `T`, under a proof obligation `r ≠ none` (obligation
  kind `option.some`). In the model, `value` is junk-on-none
  (`Option.getD default`) — the same convention as `Seq.get` off-range,
  where a bounds VC keeps verified code away from the junk. The default
  belongs to the payload type (`0` for integers, `false` for `Bool`).
  `sable test` traps on `.value` of a `none`, exactly as C++ `value()`
  throws.

The prelude (`lean/Sable/OptionAcc.lean`) defines `Option.is_some`
(`o ≠ none`, a Prop) and `Option.value` (`getD default`), so **the same
postfix syntax elaborates in clause text**: new contracts can be
written accessor-style —

```
/// post result.is_some → result.value = 7
```

— instead of `match result with | some v => …`. The match idiom in
existing specs remains valid Lean and keeps working; nothing new needs
it. Program surface and spec surface converge on the accessor style.

## Consequences

- The VC for `.value` lands wherever the access happens; the branch
  that guards it (`if (r.is_some)`) provides the path fact that
  discharges it. Unguarded access is a verification error, not UB.
- Callee posts written accessor-style compose directly with caller-side
  accessor reasoning (no match-reduction plumbing). Posts written
  match-style need `Option.eq_some_of_is_some` to bridge — provided in
  the prelude.
- The interpreter and the spec monitor both understand the accessors,
  so accessor contracts are fully monitorable.

## G1.1 amendment: the first Boolean payload (2026-08-12)

G1.1 admits one complete source-to-proof-and-interpreter path for
`option<bool>` without treating that path as general aggregate support. An
ordinary function or inherent class method may return the type. Explicit and
inferred locals may receive a call result or a contextual
`some(bool-expression)`/`none`, participate in assignment, and use `.is_some`
and guarded `.value`. Calls returning `option<bool>` compose in expressions and
returns; option-typed call parameters remain excluded.

The proof type is Lean `Option Bool`, not an integer encoding. VC generation
represents a Sable program Boolean symbolically as a proposition. Constructing
`some(p)` therefore inserts an explicit
`@decide p (Classical.propDecidable p)` bridge, while reading a Boolean option
payload maps the Lean `Bool` back to the proposition `o.value = true`. This
makes both changes of representation visible at the trusted VC-generation
boundary.

The interpreter and the dynamic specification monitor retain the checked
payload type on the option value, including `none`. That metadata is what makes
the logical absent-value fallback match `Option.getD default`: integer absence
has junk value `0`, Boolean absence has junk value `false`, and an executable
`.value` on either absence still traps.

The accepted declaration surface stays intentionally narrow. Boolean arrays
and `alloc_array<bool>`, every option-typed parameter, option-valued class or
record fields, trait and impl method option returns, record and nested option
payloads, and Boolean generic arguments remain rejected. The formal SVM and LLVM emitter also
remain fail closed for `option<bool>` until their own G1.2/G1.3 slices.

G1.1's complete low-concurrency closure command was
`CARGO_BUILD_JOBS=1 CARGO_INCREMENTAL=0 SABLE_TEST_JOBS=1 SABLE_LEAN_JOBS=1
SABLE_REQUIRE_CLANG=1 cargo test -j1 -- --test-threads=1 --nocapture`. It passed
116/116 library tests; all 374 corpus subjects (80 verifies, 231 must-fail, 45
dynamic, 18 dynamic-fail) in 409.31s; the focused `option_bool` verification at
21/21 obligations across six functions and its dynamic subject at 1/1; LLVM CLI
6/6; the exact `VerifiedProgram` interpreter↔Clang differential at `-O0` and
`-O2` 1/1; and SVM differential 69/69. The randomized allocator,
grind-budget, LSP, and documentation gates were green. G1.1 is closed.
