# ADR 0029 — Destruction semantics and resource fields

**Decided 2026-08-11.** `deinit` bodies had to be empty. Several earlier
rungs deferred to this one by name — RAII resource classes, mutable field
borrows, `partially-moved` in the place engine — so this decides the
semantics *before* lifting the restriction, which is the order
`docs/notes/unsafe-plan.md` insisted on.

## Decision

**A destructor differs from a method in exactly the ways "the value ceases
to exist" implies.**

1. **The class invariant holds on entry and is not re-established.** There
   is nothing left to hold it. A `deinit` therefore owes no `inv_exit`
   obligation, and it has no `_old_self` twin either: there is no "after"
   to compare against, so `old self` would name nothing.

2. **The body may move fields out.** That is how a class that owns
   authority hands it on. The *field* is the place that dies, not the
   object, so the untouched siblings stay readable — which is what
   `partially-moved` means, and what a destructor that consumes one field
   and reads another needs.

3. **A moved field is not dropped again**, and the rest drop in reverse
   declaration order.

4. **The order within a drop is invariant → body → remaining fields.**
   Checking the invariant after the body would evaluate it over a hole the
   body just made. This is a dynamic-monitor rule, and it was
   unambiguous-by-accident while bodies were empty.

5. **Classes may hold resource fields**, and `#[must_consume]` marks one
   whose authority must be handed on. Abandoning it is a diagnostic
   (`resource.abandoned`), as is putting one on a class with no destructor,
   since then every value would abandon it. An **ordinary** affine resource
   field may be abandoned: that is a leak, and affine-not-linear authority
   permits leaks. The marker is what turns a permitted leak into a
   diagnosed one.

6. **`#[must_consume]` applies only to resource fields.** An ordinary value
   has no authority to hand on.

## Three corrections to earlier rungs

This rung's most useful output is what it invalidated.

**ADR 0023's mutable field borrow is sound in a destructor.** `&mut a.f`
was deferred because a callee handed it could not re-establish `a`'s
invariant, which may constrain that field against its siblings. In a
`deinit` there is no invariant left to break — so the reason evaporates
exactly where the invariant does. `&mut self.w` is how the destructor hands
its world to `posix_close`, and it is legal there and nowhere else.

**ADR 0027's brand argument stopped being true.** It reasoned that only a
raw or resource *return type* could launder a loan brand out of an
exposure, because Sable had no globals and no storage-typed fields.
Resource fields make a class exactly such a container: a function returning
one can carry borrowed storage out. `class_holds_storage` now decides it,
transitively through class fields, and
`corpus/must-fail/expose_launder_via_class.sable` is the guard. The lesson
is not that the earlier argument was careless — it was correct when made —
but that an argument from "the language has no X" expires when X arrives,
and the ADR that made it should be re-read when it does.

**`havoc_mut_borrow_args` assumed a borrow names a whole place.** `&mut
self.w` replaced `self` with a view and lost the self-chain, which showed
up as an `unreachable!` in `self_chain`. A field borrow now writes the
fresh state back into the base object, leaving every sibling where it was.

## Consequences

- A by-value class argument removes the value from its source place in the
  interpreter. This was harmless while destructors were empty — the
  invariant check was merely repeated — and a real double drop now that
  bodies run.
- Resource fields contribute their *view* to the class structure in Lean.
  The authority stays a checker property, so a class gains a value and no
  obligation.
- `resource.in_class` is gone: it named precisely this restriction.
- `Ctx::is_partially_moved` was deleted rather than kept behind an
  `allow(dead_code)`. Only `self` can be partially moved today, and `self`
  is not usable as a whole (no `return self`, no `&self`), so the query has
  no reachable caller. It is three lines to restore when whole-object uses
  of a partially-moved value become expressible.

## Deliberately not decided

- **A leak *warning* for abandoned unmarked fields.** The plan allows one.
  Nothing warns today: the diagnostic exists only for `#[must_consume]`,
  which keeps the signal high while the surface is small.
- **`#[must_consume]` on locals and parameters**, which is where it would
  catch a forgotten `close` at a call site rather than in a class. That
  needs the same marker on a *type*, not a field, and is a larger question.
- **Drop order across a partially-moved class field.** A class field that
  the body moved out is skipped; a class field the body moved *into* is
  dropped where it now lives. Nested partial moves (`self.a.b`) are not
  expressible, so the recursion is one level deep in practice.
