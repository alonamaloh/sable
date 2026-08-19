# ADR 0093 — owner slots are not copy arrays

**Decided 2026-08-19; implementation in progress.** Generic owner storage uses
an explicit occupancy-bearing `slots<T>` container. It does not widen ordinary
`[T]` arrays, copyable options, or unchecked indexed places.

## Context

The first generic `Vec<T>` benchmark predates affine owners. Its backing
`[T]` is filled by repeating `0`; indexed reads, stores, growth, and `pop` copy
elements. The interpreter likewise implements ordinary arrays with clone-based
`repeat`, `get`, and `set`. Those rules are correct only for the existing
copy-element domain.

The recursive generic-type representation can already spell class arguments,
and `Ty::is_affine` can recognize nested ownership. Neither fact supplies an
occupancy model. Simply admitting a class as `T` would fabricate owners in
unused capacity, duplicate them during growth, and leave moved-out cells to be
destroyed again. Adding an index projection to general `Place` would also make
the checker, proof state, interpreter, and backend rediscover a new aliasing
model before the operation that needs it is understood.

G3 therefore starts from the storage transition, not from a wider parser row.

## Decision

### A distinct container

`slots<T>` is an owned fixed-length container whose cells are either empty or
hold exactly one `T`. Its length is fixed after allocation. It is distinct
from `[T]` in the source type, checked representation, retained cleanup plan,
proof model, interpreter value, formal-machine admission gate, and native ABI.

The first surface operations are:

```sable
slots<T> values = alloc_slots<T>(length);
slot_put(&mut values, index, value);
T moved = slot_take(&mut values, index);
```

`alloc_slots<T>` creates independent empty cells; it never repeats a `T`.
`slot_take` requires an in-bounds occupied cell, removes its payload, and
returns the sole owner atomically. `slot_put` evaluates and stages its incoming
value first, requires an in-bounds empty cell, then installs the sole owner
atomically. The first Vec surface uses take-before-put for replacement, so G3
does not initially define destructive occupied-slot overwrite.

Both operations name an explicit unique borrow of the container. Their checked
identities retain the exact container `Place`, index type and source span,
payload type, operation kind, bounds/occupancy trap sites, mutation effect, and
the checker-authored value-transfer key where a payload crosses the boundary.
There is no general indexed owner `Place` and no ordinary program read or store
for `slots<T>`.

The checker treats `slot_put` as a move sink and `slot_take` as a move source.
Loop effect plans havoc the whole slots container after either mutation.
Deletion, substitution, or mismatch of the checked transition or retained
control action fails closed before proof or execution.

### Cleanup and traps

A slots owner destroys every occupied cell exactly once, in descending index
order, then releases the container allocation. Empty and already-taken cells
are no-ops. Destruction removes or neutralizes a cell before recursively
destroying its payload, so a failing deinitializer cannot leave the same owner
reachable for a second attempt.

The cleanup recipe is checker-sealed and recursive. Class leaves link to the
exact concrete `ClassDropPlan`; conditionally present payloads and containers
retain their child recipe rather than asking each consumer to classify `Ty`
again. Resource payloads remain outside implicit destruction: mandatory
resources must reach their sealed consumer.

Out-of-bounds take/put, empty take, occupied put, allocation failure, and any
recursive payload-destruction failure take exact retained terminal no-unwind
routes. A trap before installation leaves the old container state intact; a
trap during terminal scope destruction skips the remaining cleanup suffix.

### Proof model

VC generation models `slots<T>` as `Sable.Seq (Option T)`. Allocation produces
an all-`none` sequence. A successful take proves bounds and presence, returns
the present payload, and writes `none`; a successful put proves bounds and
emptiness, then writes `some value`.

For a class payload, the compiler also maintains the structural fact that
every present cell satisfies that concrete class's invariant. Allocation makes
the fact vacuous, put obtains it from the moved value, and take transfers it to
the returned value. This fact is compiler-authored and is not delegated to a
user-written Vec invariant.

The proof-level sequence may be copied as mathematical state. That does not
authorize copying the executable slots value or any present runtime payload.

### Generic instantiation and proof reuse

Monomorphization admits a non-generic concrete class as a type argument only
after resolving it to the final checked class identity. Instance identity uses
the existing injective structural `CanonicalTypeKey`; emitted names use an
injective component which does not depend on module-order class indices.
Nested generic-class owner arguments remain closed in the first tranche.

ADR 0009 integer-model proof reuse remains legal only when every argument is a
concrete integer. A specialization containing a class owner receives
`ProofReuse::None` and is checked and verified independently after full
substitution. The retained template may be checked as a non-executable source
body, but its integer-parametric proof is never evidence for an owner instance.

### Vec uses move-only common-denominator operations

The owner-capable Vec is backed by `slots<T>`. Its first common-denominator API
has `push(T)`, a preconditioned `pop() -> T`, and
`replace(index, T) -> T`. It has no shared `get() -> T`, and `pop` does not
return `option<T>`; those would respectively copy an owner or broaden the
affine-option ABI for an unrelated feature.

Growth allocates an empty larger slots buffer, then takes each live payload
from the old buffer and puts it into the new one. Only after the movement loop
completes does field replacement install the new buffer. Vec invariants state
that the prefix below `len` is occupied and the remaining capacity is empty.

## Rollout and evidence

The implementation is split into green, fail-closed commits:

1. retain one recursive value-cleanup recipe without widening admission;
2. add the `slots<T>` representation and stable parser/type gates, with every
   unimplemented downstream stage refusing it by name;
3. seal checker ownership/control actions and implement VC plus interpreter
   take/put/lifecycle semantics;
4. admit concrete class generic arguments without integer proof reuse and add
   the owner-safe Vec verification/runtime corpus;
5. add formal SVM slot transitions and the native slots ABI, then require
   interpreter/Lean-SVM and Clang `-O0`/`-O2` differential evidence.

Each admission change requires positive, must-fail, dynamic-trap, and forged
checked-AST tests. Required lifecycle cases include growth, push source death,
pop return, replace, reverse destruction, moved-cell suppression, early return,
loop cleanup, allocation failure before movement, and a trapping incoming
value which leaves the destination unchanged.

## Boundary

This decision does not make ordinary arrays affine-element containers, add
general indexed places, authorize repeated owner initialization, widen
`option<T>` calling conventions, or reuse a generic integer proof for class
owners. Until a stage consumes the exact slot/cleanup plan, it must reject the
shape with a stable named diagnostic.

The first Lean ownership-frame theorem remains a local theorem about the
existing atomic `moveLocal` SVM step. It does not by itself prove slot
transitions, Vec correctness, source-to-SVM translation, or VCgen soundness.
