# ADR 0080 — a nullable owning handle

**Decided 2026-08-18.** `option<class>` joins the affine option family:
an explicit mutable local that owns its present case, inspected with
`.is_some`, emptied with atomic `.take`, and destroyed through the
class's own destructor when dropped holding a value.
`docs/type-matrix.md` opens `class` × `option payload` (73 → 74 of 180
intended); every boundary the family closes — parameters, returns,
fields, traits — closes for the class payload automatically, each stage
answering in the affine family's own names with zero SVM or LLVM code
edits.

## Context

The affine family had one payload, the owned Boolean array, and its
recognizer was one function (`as_affine_option_payload`). A class
payload is the family's semantic test: unlike an array, its present case
carries a destructor, an invariant, and possibly must-consume resource
fields, so the wrap, the take, and the drop all touch the ownership
machinery ADRs 0029/0030 built.

## Decisions

1. **Take is skolemization.** `.take` on a class payload binds a fresh
   symbolic value through the same `fresh_state_for` Class arm every
   havoc uses — field facts and invariant included — pinned by the
   equation `old = some taken` under the proven presence. There is no
   junk default to spell for a class (emitted structures derive no
   `Inhabited`), and none is needed: the equation makes the binder *be*
   the payload. The invariant assumption is sound because the producer
   set is closed: every `some` wraps a fresh checked construction or an
   invariant-carrying named local, and every widening of that set must
   re-verify this argument. The array family's `getD` model is
   byte-identical to before.

2. **The wrap consumes its source.** `some(c)` on a named class local is
   a move (ADR 0030): the source dies, the option is the sole owner, and
   the wrapped value's destructor runs exactly once — through the
   option. The array family keeps wrapping restricted to fresh
   allocations; the class family admits fresh constructions and named
   owners, and the split is recorded here.

3. **Drop routes through the destructor, in one place.** The checker
   imposes no consumption obligation and VC generation emits nothing at
   scope exit — ADR 0029's arrangement carries the deinit — and the one
   semantic edit is the interpreter's: a present class payload routes
   Object-style through `drop_value` (invariant check, deinit body,
   reverse field drops), an absent option stays a plain unbinding, and a
   trap runs no drops at all, destructors included. The corpus pins all
   three directions dynamically: a destructor that fails a second run
   passes exactly-once, a destructor that fails any run proves the none
   drop ran nothing, and a loud destructor in `test-fails` proves the
   some drop really destroys — the two-halves discipline, because a
   compiler that destroys nothing passes the first half alone.

4. **Take binds through `var`.** A class local is `var`-introduced, so
   its extraction is too: `var t = o.take;` is the class destination,
   while the array family keeps its typed-declaration route. The take's
   result is derived from the source's payload — never hardcoded — so a
   second class cannot type-confuse the destination.

5. **The monitor's affine snapshot is payload-generic.**
   `SpecVal::AffineOpt` carries any payload snapshot, so `.is_some`,
   `= none`, and match-bound field clauses monitor for class payloads
   exactly as for arrays; `.value` stays unmonitorable for the whole
   family.

6. **No differential oracle exists for this cell.** Class values cannot
   exist in the formal machine and the backend refuses the shape, so the
   runtime semantics are pinned by the interpreter and the corpus alone —
   which is why the exact-once subjects check *behavior* (the destructor
   ran, or did not), never cross-implementation agreement.

## Consequences

`corpus/verifies/affine_option_class.sable` (34 obligations: lifecycle,
wrap-of-named, take-then-use through `some`-injectivity, take in a
loop), the exact-once tests battery (drop-while-some, take-then-drop,
source-kill, branch-divergent, none-runs-nothing), five `test-fails`
twins (both loud-destructor directions, both empty-take traps, and
trap-beats-deinit), three new fences (inference, wrap-of-take, static
presence), and the repurposed `option_payload_class.sable` pinning
declaration-site mutability. Generic templates cannot manufacture
`option<class>`: the template position gate refuses an affine option parameter,
and an owner specialization is independently rechecked rather than inheriting
the integer-model proof — a verified non-interaction.
