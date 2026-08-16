# ADR 0073 — an exposure freezes its owner

**Decided 2026-08-16.** Closes the exposure half of the two-names defect
class. ADR 0072 fenced it for borrows and named this gap as open; this
decision closes it.

## Context

`unsafe expose &a as (p, resource m) { ... }` lends an array's bytes to a
raw pointer and a resource for the body and takes them back at the end
(ADR 0026). The checker bound `p` and `m` and then checked the body with
the owner's name still live in scope. VC generation did the matching
thing: the view was bound as a snapshot of the owner's term at entry, the
owner's own entry stayed in the environment, a mutable exit overwrote the
owner from the view, and a shared exit wrote nothing back.

So inside the body the owner's name and the loan were two believed names
for one buffer, and they could disagree. This verified:

```
/// pre  a.len ≥ 1
/// pre  a.get 0 = 6
/// post a.get 0 = 1
/// post result = 6
pub fn both_names(&mut [u8] a) -> u8 {
    mut u8 seen = 0;
    unsafe expose &a as (p, resource m) {
        a[0] = 1;
        seen = raw_load8(p, &m);
    }
    return seen;
}
```

The two postconditions cannot both hold: at run time there is one buffer,
so `a[0] = 1` is what `raw_load8` sees. `sable check` proved both. Two
siblings of the same hole: a direct store into the owner beside a
`raw_store8` was silently discarded, because the mutable exit
reconstructs the array from the loan's bytes and the direct write is not
in them; and a nested exposure of the *same* array was accepted, with the
inner loan's writes discarded by the outer exit the same way.

ADR 0026 had left nested exposure deliberately undecided with the
argument that "the exposed array is borrowed, and a second mutable borrow
of it is already rejected". **That argument was wrong.** The
borrow-conflict rule (ADR 0022/0023) is consulted only within a single
call's argument list; an exposure is a statement, not a call, so nothing
ever routed a second exposure — or any direct use of the owner — through
that rule.

The proof, the interpreter, and the formal machine all model exposure as
copy-in/copy-out, and all three agree — which is exactly why no
single-pipeline check could catch this. The premise under which
copy-in/copy-out is faithful is ADR 0069's: no second name reaches the
storage while the loan is out. Exposure did not establish that premise;
this decision makes it establish it.

## Decision

**An open exposure freezes its owner's name for the body.** The checker
records the owner in a per-function map (owner name → the loan's pointer
and resource names) when the exposure opens and clears it when the body
ends. While the name is frozen, every spelling of it is refused under one
named, spanned diagnostic, `expose.owner_frozen`, whose label and note
say to use the loan and, for lengths, to bind `a.len` to a local before
the exposure.

The guard sits on every door the checker has for a name:

- reading the name as a value (`ExprKind::Var`);
- indexing and `.len` (`array_elem_ty`, shared by both);
- storing into an element (`Stmt::Store`);
- reassigning the whole name (`Stmt::Assign`);
- borrowing it, which is what passing it to a callee spells
  (`ExprKind::Borrow`);
- moving it into a field (the array-move arm of `Stmt::FieldAssign`);
- exposing it again (`Stmt::Expose`), which closes nested exposure of
  one array for free. Nested exposure of *distinct* arrays is untouched
  (`copy_prefix` is the corpus witness).

The rule refuses **every** spelling, including reads that are sound in
isolation — `a.len` cannot change while the loan is out, and refusing it
costs one hoisted local. The rule is "the owner has no spelling inside
the body", not a list of dangerous spellings; ADR 0072 records where a
list of dangerous spellings leads. Fail-closed is the point: the sound
reads have a one-line rewrite, and the unsound ones stop proving false
contracts.

VC generation is unchanged. Its copy-in/copy-out model was never the bug
— it is faithful exactly when the loan is the storage's only name, and
the checker now guarantees that before any VC is generated. Machine
semantics, the functional evaluator, and the agreement proofs are
untouched for the same reason: no admitted program changes meaning.

## What this does not do

It still builds no aliasing model, on ADR 0072's reasoning: the freeze is
a refusal keyed on a name, not a loan-liveness analysis. Together the two
rules restore the name-keyed environment's premise everywhere the
language can currently put a second name — borrows exist only where the
compiler relates them to their owner, and exposure now removes the
owner's name for exactly the region where the loan is the owner.

## Consequences

- `expose.owner_frozen` is a named, spanned refusal. Eight
  `corpus/must-fail/` subjects reach it, covering every guarded door:
  `expose_owner_write` (the contradictory-postconditions program above),
  `expose_owner_write_beside_raw` (the discarded direct store),
  `expose_owner_read`, `expose_owner_len`, `expose_owner_borrow`,
  `expose_owner_nested`, `expose_owner_assign` (whole-name reassignment),
  and `expose_owner_value_use` (the bare name handed to a callee).
- Four `corpus/verifies/` wrappers read the owner's `.len` inside their
  bodies — `copy_prefix`, `fill_all`, `checksum_all`
  (`unsafe_copy.sable`) and `read_into` (`posix_read.sable`). Their
  contracts were sound (`.len` is not a mutation channel), so each binds
  the length to a local before the exposure and verifies unchanged,
  manual discharge included. `corpus/tests/test_unsafe_copy.sable` and
  `test_posix_read.sable` run the rewritten wrappers unmodified.
- ADR 0026's "deliberately not decided" paragraph on nested exposure is
  superseded: its premise about the borrow rules was false, and the check
  it asked for now exists as part of this rule. ADR 0072's open-gap
  paragraph carries an amendment pointing here.
- `docs/type-matrix.md` and `docs/shape-admission.md` do not move: the
  rule adds no type, no position, and no stage-gate column — it consults
  a per-body flag on paths every shape already goes through.
