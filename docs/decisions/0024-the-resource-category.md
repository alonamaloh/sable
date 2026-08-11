# ADR 0024 — The resource category

**Decided 2026-08-11.** ADR 0022 fixed the metatheory unsafe Sable is
built against; ADR 0023 built the place/borrow engine on ordinary class
values. This decides how the third value category appears in the
compiler — the surface, the type, and what each stage is allowed to know
about it. It does not add raw memory: nothing here can allocate a span,
load a byte, or store one.

## Context

`docs/notes/unsafe-sketch.md` bets that **authority can be a checker
property while the logic reasons only about pure values**. ADR 0022
proved the interpretation that bet needs (`Own (rawHeap, Δ)`) in
`docs/notes/unsafe-probe.lean`. What was missing was the compiler side:
a category the checker tracks affinely, which vcgen sees only as a value,
and which the runtime does not see at all.

## Decision

**A resource is authority; its *view* is an ordinary value; the two are
separated by which language may read them.**

1. **The view is ghost.** A clause may say `s.len`; program code may not
   (`resource.view_is_ghost`). This is the load-bearing line. A program
   able to read the view would need it at runtime, and a runtime view is
   a thing a program could construct — which is exactly the authority
   forgery the category exists to prevent. It also makes erasure real
   rather than aspirational: there is nothing left to pass.

2. **`Ty::Res(k)` and `Ty::ResRef(k, m)`**, spelled `resource RawSpan`,
   `resource &RawSpan`, `resource &mut RawSpan`. The category is written
   at every binding site — parameter, return, local — because a reader
   must not have to infer "this is authority" from a callee's signature.
   The borrow marker sits *inside* the category (`resource &mut R`, not
   `&mut resource R`) so the category is the first thing read.

3. **`RawSpan` is compiler-defined.** A program cannot declare a resource
   type (`resource.unknown_type`). User-defined resource types wait until
   the memory core is stable, and when they arrive they must have no
   ordinary public constructor.

4. **Ownership is U2a's engine, unchanged.** Moves, borrows, borrow
   conflicts, and use-after-move are the same `Place` set and the same
   `check_borrow_conflicts`; the resource-specific work is two extra
   diagnostics and one type test. There is no second ownership system,
   which was U2b's stated exit criterion.

5. **Branch and loop *shape* is stricter than for classes.** Where a
   class moved on one reaching branch is simply dead below, a resource
   moved on one branch and not the other is rejected
   (`resource.branch_shape`), and a loop body that consumes a resource
   live at the head is rejected (`resource.loop_shape`). The reason is
   not soundness — dropping a resource is permitted, and leaks are not
   unsoundness — it is that with authority, the difference between "I
   released it deliberately" and "I forgot on one path" is worth a
   diagnostic. Views may change freely across both; the invariant carries
   them.

6. **In the logic, a resource is a view binder and nothing else.** No
   generated VC mentions a heap, a capability, or disjointness.
   `resource &mut R` follows the `&mut` array rule — entry state as the
   binder, current state in the env, `old s` resolving to the binder — so
   it needed no new machinery at all: the same `entry_states` map and the
   same `havoc_mut_borrow_args` that serve `&mut [T]` and `&mut C`.

7. **`lean/Sable/Raw.lean` holds the views, not the interpretation.**
   ADR 0022 said the model graduates from `docs/notes/` when the compiler
   emits against it. What the compiler emits against is `SpanView` and
   `ByteState`; `Own`, `Cap`, `Disjoint`, and the preservation theorems
   stay in the probe until raw operations exist to be justified.

## Consequences

- **Views are per-binding-site well-formed, not invariant-carrying.** A
  span view gets `0 ≤ len ∧ len ≤ bytes.len` at every binder, the way a
  borrowed array gets its length and element facts. There is no
  user-written invariant on a resource and so no `ret_inv` analogue —
  which is the difference between a class (whose invariant somebody must
  re-establish) and a resource (whose well-formedness is structural).
- **Class members may not take resources** (`resource.in_class`). Putting
  authority inside a class needs destruction semantics — what happens to
  the token at drop — and that is an unbuilt prerequisite, not a default
  to pick silently.
- **Erasure is implemented but not yet exercisable end-to-end.** Resource
  arguments are dropped from interpreter call arguments and from the
  callee's runtime parameter list, on both sides by the same filter. No
  test can reach that code, because nothing can *create* a `RawSpan` yet
  — allocation is U3. Stated rather than claimed.
- `type.class_arg_borrow` and `type.class_borrow_mutability` became
  `type.arg_borrow` and `type.borrow_mutability`: the rule is about
  borrows, and it now has two categories under it.

## Deliberately not decided

- **Raw operations.** `load8`, `store8`, `take8`, `copy_nonoverlapping`,
  and allocation all need the byte heap in the formal SVM (U3). Until
  then a `RawSpan` can be moved, borrowed, and described, and that is
  all — which is precisely enough to shake out the ownership rules.
- **`split_off` and `join`.** The two pure authority redistributions.
  `SpanView.take`, `.drop`, and `.cat` are already in the prelude with
  their length and byte lemmas, so the remaining work is the sealed
  operations and their contracts.
- **Resource fields, aggregate resources, and typed cells.** Scoped out
  of this slice on purpose; the first two need destruction semantics and
  the third needs a modelling probe of its own (ADR 0022's open
  question 5).
