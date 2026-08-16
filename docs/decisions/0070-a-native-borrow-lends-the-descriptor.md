# ADR 0070 — a native borrow lends the descriptor

**Decided 2026-08-16.** Extends ADR 0068 to the LLVM emitter, and states why
the native convention for a unique borrow is not the formal machine's
(ADR 0069) even though both are faithful.

## Context

Two halves of this already existed and neither was the hard part.

An owned `[bool]` local has a native representation: `%sable.array.bool =
type { ptr, i64 }`, canonical zero/one `i8` element bytes, storage from the
versioned `__sable_rt_array_alloc_v1` / `__sable_rt_array_free_v1` hooks with
a null/zero descriptor for length zero, a 50,000,000-element cap, trap kind 9
for allocation failure and kind 10 for a bounds failure (ADR 0059).

A borrowed `[u32]` parameter has a calling convention: N0 passes
`%sable.array.u32` by value, admits an argument only when it is the exact
explicit named borrow with matching mutability, and keeps a borrowed
descriptor out of the cleanup registry entirely.

What stood between them was one accessor. `is_owned_bool_array` is
`Ty::is_owned_array_of(&Ty::Bool)` — strict about the binding mode — and it was
being asked *every* Boolean-array question: the IR type, the element bytes, the
store target, the index and length bases. It is the right question for
ownership and the wrong question for representation, and asking it once for
both is what made `&[bool]` have no LLVM type at all. `is_u32_array` had
already been split the other way (`is_array_of`, borrow-transparent), which is
why the `u32` row of `docs/shape-admission.md` reads `llvm parameter: yes`
while the `bool` row read `backend.unsupported`.

## Decision

**A borrow lends the descriptor. The IR type of a borrowed array is the IR
type of the array; only the mangled symbol knows the binding mode.**

`llvm_ty` answers `%sable.array.bool` for `[bool]`, `&[bool]`, and
`&mut [bool]` alike — the same rule ADR 0067 gives `lean_ty`, for the same
reason: a borrow is a second name for storage, not a second shape of it. The
emitter therefore gained no new type, no new hook, no new trap kind, and no
new element encoding.

The split that makes this safe is the one ADR 0068 made in VC generation and
ADR 0069 made in the SVM bridge, applied here:

- `is_owned_bool_array` — strict — keeps deciding *ownership*: which
  declarations allocate, which enter the lexical cleanup registry, and which
  call the free hook.
- `is_bool_array` — borrow-transparent — decides *representation*: the IR
  type, the descriptor loads, the element addressing, the index and length
  bases.

A parameter of borrowed type therefore never enters a cleanup scope, exactly
as `&[u32]` never does, and the double free is unwritable rather than merely
unwritten.

**Write-through is the shared data pointer, not a copy-out.** The callee
stores the lent descriptor in its own slot; that copy holds the *caller's*
data pointer, so `flags[i] = true` inside the callee writes the caller's bytes
during the call. Nothing is copied back, because nothing was copied. The
callee cannot change the length or the allocation: the descriptor is a value
and reallocation is not in the borrowed surface.

**This is deliberately not what the formal SVM does.** ADR 0069 models a
unique borrow as copy-in/copy-out — `Arg.lend` records a loan and `Env.restore`
writes it back at the pop. The two are different mechanisms and both are
faithful, for the same reason: a unique borrow is exclusive, so no observer
can distinguish a cell written during the call from one restored at the end of
it. The machine picks the formulation whose agreement proof is a total
function both the rules and the evaluator name; the backend picks the one the
hardware already has. Neither is the definition of the other, and
`corpus/llvm-diff/bool_array_borrows.sable` is where the interpreter's answer
and the native one are compared rather than assumed.

**The mangled component generalizes.** A borrowed array's symbol component is
`a` + the element's code + `s` or `m`: `au32s`, `au32m`, `abs`, `abm`. Two
functions differing only in a parameter's borrow mutability remain two native
entry points, even though the IR type does not distinguish them. This spelling
is internal and versionable, like the named type — every generated function and
type stays module-internal, and no cross-module, Sable, or C ABI follows.

## Consequences

### What the emitter admits

`&[bool]` and `&mut [bool]` as parameters of internal ordinary functions, with
the same argument rule N0 states for `&[u32]`: the checked argument must be the
exact explicit named borrow with matching mutability, a `&mut` may not be taken
through a non-mutable place, and overlapping mutable aliases in one call remain
rejected. A reborrow — `&flags` or `&mut flags` where `flags` is itself a
borrowed parameter — is admitted, because the source place is an array in a
binding mode that permits it.

The store rule now asks the question it means: writing needs the exclusive
right to the storage, which a `mut` owner and a unique borrow have and a shared
borrow does not. That replaces an owner-plus-one-spelling allow-list, so
`&[u32]` is refused as a shared borrow rather than as an unrepresented type.

### What stays closed

Owned array parameters and returns, array-valued entries, fields, classes,
methods, externs, public or cross-module ABI, other element widths, whole-array
transport, exposure, generic containment, and option containment. `[bool]`'s
`llvm parameter` cell stays refused: an owner does not cross a call boundary,
and the parser refuses to let one be written there.

### Table movement

`docs/shape-admission.md` moves exactly two cells: `&[bool]` and `&mut [bool]`
× `llvm parameter`, `backend.unsupported` → `yes`. Those rows now match
`&[u32]` and `&mut [u32]` in all three LLVM columns — runtime type and local
still refused, parameter admitted. `docs/type-matrix.md` does not move: the
backend is not on the verification path, so no source program's answer
changes.

### Evidence

`corpus/llvm-diff/bool_array_borrows.sable` verifies at 25 obligations across
10 functions and is compared, entry outcome for entry outcome, against Clang
`-O0` and `-O2`. Its entry reads back through the owner what a callee wrote
through a `&mut` parameter, passes shared and unique reborrows on by name,
lends a literal, and lends a zero-length array. The `llvm_cli` fixture pins the
descriptor-by-value signature, both mangled components, and — with strong hooks
that abort on a free of unowned storage — that no borrowing function reaches
the free hook, that the empty array allocates nothing, and that a bounds
failure through a borrow is kind 10 with `(0, index, len)` at both
optimization levels.
