# ADR 0007 — Traits v1: law-carrying bounds for generic verification

Date: 2026-08-09. Status: accepted.

## Context

The hash map (Tier 1) needs a generic `HashMap<K, V>` whose *class
invariant* talks about the bucket of each stored key — every occupied
slot must be reachable from its key's home bucket through occupied
slots. That invariant must apply the key type's hash function **at the
specification level**: `get` is only allowed to stop at the first empty
slot because the hash it computes today equals the hash `insert`
computed yesterday. A contracted program function is not enough — two
calls of `K::hash(k)` yield two result symbols related only by their
postcondition, and no postcondition of the form `P(result)` can supply
*determinism across calls*. The spec needs hash to be a **function**.

## Decision

A trait declares, per method, a pair: a **spec-level function** and a
**program function contracted against it**.

```
trait Hashable {
    /// spec hash : int → int
    /// post 0 ≤ result
    /// post result = Self::hash x
    fn hash(Self x) -> u64;
}
```

- `/// spec hash : int → int` declares a Lean-level function symbol.
  Within the trait's clauses it is referenced as `Self::hash`; within a
  bounded template as `K::hash` (for `K: Hashable`).
- The program method's contract may (and for hash, must) tie its result
  to the spec function. That equation is the *law*: it converts the
  opaque call results into applications of one function, restoring
  determinism, substitutivity (`k1 = k2 → hash k1 = hash k2`), and
  spec-level reasoning.
- `Self` is the implementing type inside a trait; it is type-parameter
  machinery under the hood (`TParam(0)`), so the whole generics v1
  substitution pipeline applies unchanged.

An impl provides the spec function as an ordinary **ghost def** (same
`/// def` fragment as module-level ghost definitions — Lean-emittable
and runtime-monitorable) plus program bodies. Contracts come from the
trait only; impl bodies must not declare their own clauses.

```
impl Hashable for i32 {
    /// def hash (x : int) : int := x + 2147483648
    fn hash(i32 x) -> u64 {
        i64 y = widen<i64>(x) + 2147483648;
        return narrow<u64>(y);
    }
}
```

Monomorphization consumes traits and impls entirely:

- Each impl ghost def is hoisted to a module ghost def under a mangled
  name (`Hashable_i32_hash_spec`); each impl body becomes a plain
  top-level fn (`Hashable_i32_hash`) carrying the trait's contract with
  `Self → i32`, `Self::hash → Hashable_i32_hash_spec` substituted — and
  is then **verified like any other function**. A lying impl is a
  failed obligation, not a runtime surprise.
- Type parameters take bounds: `class HashMap<K: Hashable, V>`.
  Instantiating with a type that has no impl is `mono.unsatisfied_bound`.
- In a bounded template, `K::hash(x)` in program text resolves to the
  impl's fn; `K::hash e` in clause text resolves to the impl's spec
  def. One surface name, two layers — the trait's law is exactly the
  statement that the pun is sound.

## Scope limits (v1, like ADR 0006)

- Bounds range over the eight integer types (whatever generics v1
  admits as type arguments).
- One bound per parameter; no trait inheritance; no default bodies.
- Trait spec functions have no `variant`s — non-recursive ghost defs
  only, so unfolding stays automatic and monitoring total.
- Laws live in method contracts. Free-standing trait laws relating
  several methods (e.g. `Eq` congruence) wait until something forces
  them.

## Consequences

- No dictionary passing, no vtables — bounds are compile-time only,
  consistent with monomorphization-first. The runtime cost is zero.
- Dynamic checking monitors trait laws too: the impl-fn posts are
  ordinary posts over ghost defs the spec evaluator can expand.
- Per-instance discharge duplication (ADR 0006) now extends to
  bounded templates; template-level discharges remain future work.

## Also decided here: `narrow<T>(e)`

The hash pipeline forces the long-anticipated conversion primitive:
`narrow<T>(e)` converts any integer type to any integer type,
value-preservingly, under a proof obligation `T.min ≤ e ≤ T.max`
(obligation kind `narrow.range`). Like `widen`, it is the identity on
the Lean side; unlike `widen`, it carries a VC. In `sable test` it
traps when the value is out of range.
