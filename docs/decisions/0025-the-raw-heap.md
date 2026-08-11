# ADR 0025 — The raw heap in the machine

**Decided 2026-08-11.** ADR 0005 fixed the SVM's normative decisions for
the safe language; ADR 0022 fixed the metatheory resources are
interpreted against; ADR 0024 made resources a category in the compiler.
This decides what the *machine* does with raw memory — the component the
resource-soundness theorem will eventually connect the checker's context
to.

## Context

The SVM keeps owned arrays and classes in the value world, and every
existing rule is written against that. The question was whether adding
raw memory means reinterpreting the machine or extending it.

## Decision

**A separate raw heap component, and every safe rule preserves it
unchanged.**

1. **Pointer arithmetic is an expression, because it is pure.**
   `ptrAdd p d` carries provenance along and moves the offset. Nothing is
   dereferenced, so a pointer may leave its allocation and come back with
   no outcome at all; only a load or a store asks whether it is in
   bounds. This is what let `Eval` stay *completely* unchanged —
   expressions still have no heap, so not one existing expression rule
   was touched.

2. **Every operation that touches the heap is a statement**, A-normalized:
   `rawAlloc dst size`, `rawFree p`, `rawLoad8 dst p`, `rawStore8 p v`,
   `rawTake8 dst p`. That is the precedent calls already set (ADR 0005
   res. 4), and it confines the heap to `Step`.

3. **A pointer is provenance plus an offset, never an address.**
   `Val.ptr alloc off`. Two live pointers may name the same machine
   address only if they name the same allocation — which is what makes
   `free` able to invalidate exactly the pointers derived from what it
   released.

4. **A freed allocation is marked dead, not removed.** Its id is never
   handed out again, so stale provenance stays distinguishable from fresh
   provenance. This is what makes a double free `undef` rather than
   indistinguishable from freeing an id that was never allocated, and it
   is why the fresh-provenance counter only ever increases.

5. **Rule side conditions are decidable predicates, not existentials over
   the heap**: `RawHeap.loadByte : Option Int`, `RawHeap.freeable : Bool`,
   `RawHeap.inBounds : Bool`. Written the other way first, the agreement
   proofs needed case analysis on inaccessible implicit binders — but the
   real argument is normative, not tactical: these are exactly the
   questions the machine must *compute* to tell a store from `undef`, so
   the rules should ask them that way.

6. **Uninitialized is a distinct byte state** (`RawByte.uninit`). It is
   what makes "in bounds, live, and still nothing to read" expressible,
   and it is not `option`: an initialized byte holding any value must
   stay distinguishable from storage that was never written.

7. **`take8` moves a byte out; it does not poison the storage.** The read
   returns the byte and leaves the location uninitialized, so reading it
   again is `undef` — until it is written back, which makes it readable
   again.

8. **Invalid raw operations are `undef`; running out of memory is a
   trap.** Out of bounds either way, a load of uninitialized storage, use
   after free, double free, freeing an interior pointer, dereferencing a
   non-pointer, and storing a value outside `u8` all reach `undef`, which
   verified code proves unreachable. Allocation past the cap is
   `Trap.oom`, because exhausting memory is a defined runtime failure and
   not a program error (§9, and consistent with `alloc_array`).

## Consequences

- **The claim that this extends rather than reinterprets is checked, not
  asserted.** The heap was threaded through the configuration in its own
  commit, with no operations at all: agreement in both directions,
  determinism, totality, and progress re-proved with no change to any
  tactic. Nothing in the safe machine's argument depends on what is in
  the heap.
- **Two layers of defence, both verified by injection.** An evaluator
  that forgets `take8`'s write-back fails the agreement proof. Changing
  the rule *and* the evaluator together consistently passes agreement and
  fails an outcome guard in `Sable/SVMRawTests.lean`. Neither layer alone
  catches both, which is the argument for having the outcome subjects at
  all rather than trusting agreement.
- **Resources do not appear in the machine.** They are erased static
  authority (ADR 0024); the resource-soundness theorem is what will
  connect the checker's context to this heap, and it is not written yet.

## Deliberately not decided

- **Alignment.** `Allocation` carries `size` and `live` but no alignment,
  because nothing in a byte-only heap can observe it. Typed storage
  (ADR 0022's open question 5) is where alignment starts to matter.
- **A source surface for the raw operations.** The subjects are written
  in the machine's own syntax, which is what this rung intended
  ("direct SVM subjects exercise the semantics"). Two of the rung's
  exit criteria as literally worded — differential subjects in
  `corpus/svm-diff`, and an injected *wrong lowering* being detected —
  presuppose a surface, and so belong with the rung that adds one. The
  ordering was discovered by building this one, and is recorded in the
  plan rather than quietly satisfied.
- **`copy_nonoverlapping`.** It needs two distinct spans and is the
  design test for whether affine tokens supply separation without a
  user-written nonoverlap formula; it waits for the operations to have
  contracts.
