# ADR 0030 — One ownership transfer, used by every sink

**Decided 2026-08-11.** ADR 0020 made class values places, ADR 0024 built
the resource category on the same engine, and ADR 0029 let destructors
run. Each rung added the sinks it needed and left the others alone, so
"what a move does" was written six times and agreed nowhere. This rung
writes it once.

## The problem, stated precisely

An external review of the destruction rung observed that ordinary function
calls removed a by-value class argument from its source place while every
other transfer still evaluated by cloning. That was accurate, and checking
it turned up more: the divergence was not a missing case in one pass but a
missing *notion* in both.

Six syntactic forms transfer ownership — a declaration, an assignment, a
field assignment, a call argument, a constructor or method argument, and a
return — and before this rung they behaved as follows.

| form | source place cleared | destination's old value destroyed |
|---|---|---|
| call argument | yes | n/a |
| `var d = a;` | checker only | n/a |
| `t = u;` | checker only | invariant checked, destructor not run |
| `self.f = x;` | no | no |
| constructor argument | checker only | n/a |
| `return x;` | no | n/a — and the local was destroyed behind it |

Every "no" was a double drop or a duplicated authority waiting for a
destructor with an effect, which ADR 0029 had just made possible.

## Decision

**A transfer is one operation with two halves, and every sink performs
both.** The source place stops holding the value; whatever the destination
held is destroyed.

In the interpreter that is `take_place` and `drop_place`, reached through
one `eval_moved` used by all six forms. Three consequences follow directly
and are not separate rules:

- **Overwriting a place runs a full drop** — invariant, destructor body,
  then the remaining fields — not the invariant check alone.
- **A returned place leaves with the caller.** The scopes unwinding behind
  it must not find the value still in its source and destroy it.
- **An owned parameter dies with the callee's frame**, after the contract
  has been checked against it, and only if the body did not hand it on.

In the checker it is `transfer`, called at the matching sinks after the
expression has been checked. It kills the source place, asks whether a
loan brand may cross this sink, and reports whether a `#[must_consume]`
obligation travelled with the value so the sink can keep it travelling.

**A contract still speaks about a moved-from parameter.** The post of an
`init` that stores its argument in a field says what the field got, so the
monitor keeps a by-value parameter's entry value after the authority has
gone. That is ADR 0024's split seen from the other side: a value outlives
the transfer of authority over it.

## What the pass found

**`self.f = x` marked nothing.** A class could take a resource into a
field while the caller still named it — `self.span = s; eat(s);` verified.
This is duplicated authority through the one sink that had no rule, and it
is the sharpest thing here.

**An owned array moved into a field kept its old name alive.** Both names
reach the same elements while the logic treats them as separate values, so
`self.buf = nb; nb[0] = 99;` made a *verified* post false at runtime. The
v1 comment describing this as "not tracked" was documenting an
unsoundness, not a limitation. Owned arrays are affine for a different
reason from resources — shared storage rather than authority — and get
their own diagnostic (`array.use_after_move`) saying which.

**`return self.f` handed a field's authority to a caller who still holds
the object.** Calling the method twice yielded two tokens for one field.
The rule now is that **a member may move a field out, but must put
something back before it exits** (`class.field_not_restored`): the class
invariant is stated over every field, and an invariant over a hole is not
a question with an answer. Replacing authority — take the old value out,
store the new one, return what was taken — is legal and is the shape a
member should use. Only a `deinit` may leave a hole, which is ADR 0029's
rule and, exactly, its reason.

**The loop-shape rule was resource-only.** ADR 0024 rejected a body that
consumes a token live at the head because the second iteration would not
have it. That argument never mentioned authority: a class value consumed
by a loop body is missing on the second iteration too, and the
interpreter's frame lookup would fail on it. The rule is now about affine
shape, and the diagnostic names the category (`resource.loop_shape`,
`class.loop_shape`, `array.loop_shape`).

**`#[must_consume]` meant "moved somewhere".** A destructor could satisfy
it by moving the field into a local and abandoning the local, which is the
leak the marker exists to diagnose. The obligation now **travels with the
token** through declarations, assignments, and fields, and is discharged
only by passing the value to something that takes it. This is what ADR
0029 listed as the honest reading, and `SystemDealloc` will need it.

**Adoption did not spend the world's claim on a descriptor.**
`open_file(&mut w, fd)` minted a fresh token each time, so affinity
stopped a program reusing one token but not making a second beside it.
`PosixWorldView` gains `claimed`, adoption's precondition becomes
`available` (open, and not already handed out), and the effect is stated
functionally as `w.claim fd` — the form ADR 0026 found necessary for
`grind` to use it without case analysis. The monitor keeps a claimed set
and traps independently, the same two layers the raw operations have.

**Three ICEs, all reachable from ordinary source**: a method assigning a
resource parameter to a resource field, a call to a method returning a
class or a resource, and a function returning `raw<u8>`. Each was a
missing match arm rather than a missing design, and the method paths now
mirror the function ones exactly. A raw *return* has no corpus subject
that verifies, and honestly cannot have one yet: the only source of a
pointer is an exposure, and a raw-returning signature launders a brand, so
the guard for it is a `must-fail`. It becomes reachable with allocation.

## Testing exact-once

"No value is destroyed twice" is what the transfer paths needed, and a
compiler that destroyed *nothing* would satisfy it. The corpus therefore
carries both halves:

- `corpus/tests/test_ownership.sable` moves a value through each form and
  drops it. Its `Token`'s destructor **falsifies its own invariant** — legal,
  since a destructor owes no exit invariant — so a second drop traps on an
  invariant the first one broke. Passing means *at most once*.
- `corpus/test-fails/deinit_runs.sable` gives a destructor a failing call
  and asserts the failure on each path. That is *at least once*. It cannot
  live in `corpus/verifies`, because a verifying file may not contain a
  deliberately failing call.

## Second pass: four places the sweep did not reach

A follow-up review of the first pass found four more, each the same rule
missing from one more spot. They are recorded here rather than in a new
ADR because they decide nothing new — they are what "every sink" and
"exactly once" already meant.

**A marker block is not a scope, and now the interpreter agrees.**
`unsafe { ... }` and an exposure body license operations; the checker
keeps their locals in the enclosing function (ADR 0026). The interpreter
ran them through the scoping `exec_block` and destroyed class values at
the closing brace, so a value declared inside one and used after it was
accepted by the checker and **panicked** the monitor. The two sides cannot
differ, and the checker's answer is the language's: `exec_open_block`
runs a marker block's statements while its declarations accumulate in the
enclosing scope's drop list.

**An inferred declaration lost the loan brand.** `raw<u8> q = raw_offset(p, 0)`
computed the brand; `var q = raw_offset(p, 0)` stored `branded: false`, so
one inferred binding laundered what the recursive `brand_of` had just been
taught to see. The comment above it claimed the opposite, which is the
failure mode the corpus exists to catch.

**A discarded class-valued result was never destroyed.** `produce();` as
an expression statement built a temporary and dropped the value on the
floor without running its destructor. A temporary is an owned value with
no place, so it is the one drop that cannot go through `drop_place`: it
dies at the end of the statement that made it. Rejecting class-valued
expression statements would also have closed it, but destroying the
temporary is the rule the rest of the language already follows.

**`#[must_consume]` could be overwritten.** The obligation travelled, but
assigning over a place that still held one silently replaced it with
whatever the right-hand side carried. The rule is now that **a live place
holding a must-consume token may not be assigned to**: consume it first,
which empties the place, and an empty place may be given a new value. The
same applies to a marked field, and marked fields now carry their marker
in *every* member context rather than only in the destructor — which is
also what lets a method that moves the authority into a local and
abandons it be diagnosed.

**A limitation, stated rather than implied.** Passing a marked token by
value discharges the obligation, and the callee's parameter does not
inherit it. So `#[must_consume]` currently means *must leave this frame*,
not *must reach a consuming primitive*: a do-nothing sink function
satisfies it. That is acceptable while the marker lives on a field, and it
has to change before `SystemDealloc`, which needs the marker on a type.

**The extern nonescape argument was stated too strongly** (ADR 0027, and
repeated in the checker). "A callee that cannot return storage cannot
retain it" is compiler-checked for a *verified* callee — Sable has no
globals, so the pointer dies with the frame — and an **audited promise**
for a foreign one, since nothing stops C stashing it in a foreign global.
The rule and the code are unchanged; which side of the audited boundary
the reasoning sits on is not. ADR 0027 carries the amendment.

## Consequences

- `Ctx::place_ty` replaces the per-category place queries; `affine_kind`
  picks the diagnostic prefix, so a category added later gets its name
  from one place.
- Field assignment revives the field's place, which is what makes
  take-then-replace expressible at all.
- `self_field_ty` splits: reading or writing *through* a field requires it
  to be live, while rebinding it does not — assignment is how a hole gets
  filled.
- A declaration is a sink like any other, so `var x = self.f;` moves the
  field. Previously only a bare local was recognised.
- `PosixWorldView` gained a field, so every world contract is against the
  new structure; the extern posts that frame `data` and `fds` are unchanged
  because nothing foreign may change who holds authority.

## Deliberately not decided

- **Partial moves across a call.** A member may not leave a hole in `self`,
  which is a restriction and not a theory. Tracking which fields a callee
  moved out would need the typestate in the signature; nothing forces it
  yet, and the replace shape covers the cases that arise.
- **`#[must_consume]` on locals and parameters.** The obligation travels
  *within* a body; passing a token by value discharges it, and the callee
  is not asked to honour it. That still needs the marker on a type rather
  than a field, as ADR 0029 recorded.
- **Releasing a descriptor's claim.** `close` consumes the token but does
  not return the descriptor to the world's available set, so a descriptor
  is adoptable once in a world's life. Re-adoption after close would need
  the world to model closure, which the crude `0 ≤ fd < fds` view does not.
- **Block scoping for locals.** Locals are function-wide in the checker;
  what stops a use after an `if` or loop body is the initialization
  analysis, not a scope. The interpreter drops at those braces, which
  agrees because a value it destroyed is one the checker will not let you
  name. Marker blocks are the case where the two really did differ, and
  that is now fixed; a genuine scope construct is still not needed.
- **A callee inheriting a `#[must_consume]` obligation.** The marker is on
  a field, so passing the token by value discharges it. Making it mean
  "reaches a consuming primitive" needs the marker on a *type*, which is
  the same prerequisite ADR 0029 recorded and which `SystemDealloc` will
  force.
