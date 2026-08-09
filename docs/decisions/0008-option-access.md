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
  (`Option.getD 0`) — the same convention as `Seq.get` off-range, where
  a bounds VC keeps verified code away from the junk. `sable test`
  traps on `.value` of a `none`, exactly as C++ `value()` throws.

The prelude (`lean/Sable/OptionAcc.lean`) defines `Option.is_some`
(`o ≠ none`, a Prop) and `Option.value` (`getD 0`), so **the same
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
