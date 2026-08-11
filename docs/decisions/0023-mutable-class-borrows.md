# ADR 0023 — Mutable class borrows

**Decided 2026-08-11.** ADR 0010 introduced `&C` and deferred `&mut C`;
ADR 0020 made places the unit of ownership and deferred it again. The
place engine now exists, so this decides what `&mut C` means, what it
does *not* reach, and why.

## Context

Before this, the only way to change a class value from outside the class
was to build a new one. `Integer::negate` copies a magnitude to flip a
sign; every arithmetic operation returns a fresh value. That is a real
cost, but the reason to build `&mut C` now is a different one: it is a
safe-side consumer of the place/borrow engine with an existing corpus to
shake it out on, before the resource category adds erasure and view
versioning on top (`docs/notes/unsafe-plan.md`, U2a).

The question `&mut C` forces is not aliasing — the place engine already
answers that. It is **who re-establishes the class invariant**. A `&mut`
argument comes back in a fresh state, and the caller assumes the class
invariant of that state. Something has to have proved it.

## Decision

**A `&mut C` parameter grants unique access, and the only way to mutate
through it is to call one of the class's own `&mut self` methods.**

Everything else follows from that sentence:

1. **The caller's post-call havoc is sound because the callee's mutation
   points are the class's own methods.** Each `&mut self` method carries
   an `inv_exit` obligation, so the invariant holds after every mutation
   the callee could have performed, hence at the callee's exit. This is
   the same closes-by-assumption argument ADR 0010 makes for `borrow_inv`
   and `ret_inv`, and it is why the restriction to methods is load-bearing
   rather than stylistic.

2. **A shared borrow does not admit a `&mut self` method**
   (`mut.method_shared_borrow`), and a shared borrow cannot be upgraded
   (`type.mut_borrow_shared`). Unique access is only ever narrowed.

3. **`&mut a.f` is rejected** (`class.mut_field_borrow`). A callee handed
   unique access to one field of `a` has never heard of `a`'s class, and
   `a`'s invariant may constrain that field against its siblings — so
   nobody re-establishes it. The place machinery supports the borrow; the
   invariant discipline does not. Mutating a field goes through a method
   of `a`, which is exactly the party that knows the invariant.

4. **Handing a class value to a borrow is written at the call site, with
   its mutability** (`type.class_arg_borrow`,
   `type.class_borrow_mutability`) — the rule array borrows already
   follow. Passing along a *shared* borrow already held under the same
   type needs no `&`: nothing is handed over that the caller did not have.
   Unique access is always spelled `&mut`, which conflict detection and
   the caller's havoc both rely on.

5. **In the logic, `&mut C` is `&mut [T]` with a structure instead of a
   sequence.** The callee's binder is the *entry* state `_old_p`; the
   current state lives in the symbolic environment and is replaced at
   each mutating call; `old p` in a clause resolves to the binder. One
   map (`entry_states`) serves `&mut` arrays, `&mut C`, and the `self` of
   a `&mut self` method, because they are the same construct.

6. **A loop rebinds a `&mut C`'s view, never the borrow.** The havoc set
   treats a borrowed class exactly as an owned local: fresh state, class
   invariant assumed, facts about the old state dropped. What the code
   after the loop knows is what the loop invariant says.

Class borrows are also permitted on methods and inits, shared or mutable,
with the same treatment as at a function call. That was previously
accepted by the checker and reached an `unreachable!` in vcgen; the
argument machinery is now shared between all three call forms.

## Consequences

- `Ty::ClassRef` carries a `Mutability`, so class borrows and array
  borrows are spelled the same way in the type. `&class` and `&mut class`
  are distinct types with no coercion between them.
- Construction now owes `borrow_inv` for its borrowed class arguments,
  which function and method calls already did. Inits were the one call
  form that assumed a borrowed argument's invariant without asking for it.
- `Integer::negate_in_place` is the first library operation that mutates
  instead of allocating. The sign flip lives in a `&mut self` method whose
  precondition (`natVal self.mag.limbs ≥ 1`) is what keeps the
  no-negative-zero invariant true, which is the discipline working as
  designed: the class states the condition under which its own mutation
  is legal, and the free function's job is only to check it.

## Deliberately not decided

- **Mutable field borrows.** Deferred on the invariant argument above,
  not on missing machinery. Lifting it needs a story for suspending a
  base object's invariant across a borrow and re-establishing it when the
  borrow ends — a real design, and one the resource category may answer
  differently.
- **Partial moves out of class fields.** Still U7a; `Ctx::is_partially_moved`
  exists and nothing produces field moves yet.
- **Borrows that outlive a call.** A borrow is an argument, not a value:
  there are no borrow-typed locals, returns, or fields, so borrow state
  never has to be tracked across statements. That is what keeps the
  engine's state per place rather than per lifetime.
