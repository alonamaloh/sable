# Unsafe Sable — design and implementation plan

*Status: implementation proposal, 2026-08-11. The architecture is concrete
enough for a prototype; the surface syntax stays provisional until the first
vertical slice works.*

*This is the **specification** half of a pair. The **argument** —  the forcing
examples, why this decomposition rather than another, and the questions still
open to taste — lives in `docs/notes/unsafe-sketch.md`, which this document
assumes and does not repeat. Read that first if you want to disagree with the
design; read this one to build it. When U1 concludes, the chosen interpretation
becomes an ADR, and that ADR supersedes both on the points it decides.*

*Provenance: a first draft argued from systems examples (Claude); an external
design review proposed the affine-resource architecture (GPT-5.6); a synthesis
adopted it as the spine; this specification is the third round, with amendments
from a fourth (loops as a metatheory obligation, destruction semantics, the
place-engine split, the manifest/hash decision). Where the rounds disagreed the
disagreement is recorded rather than smoothed.*

*Companion to the language design's memory-model, escape-hatch, SVM, and
profile sections; the allocator benchmark in the goals document; ADR 0011
(grind heartbeat budget), ADR 0017 (SVM semantic oracle), ADR 0018 (separate
verification), ADR 0020 (class values as places), and ADR 0021 (`Integer` and
path-sensitive affinity).*

## Current repository state

Two developments since the first unsafe sketch materially improve the starting
point without changing its central design.

- **ADR 0020 landed class values as places.** Sable now has class-valued fields,
  by-value class parameters that consume their argument, and borrows of class
  fields. This demonstrates the key split unsafe Sable relies on: a move and a
  borrow carry the same logical value and invariant; their difference is in the
  checker-side ownership discipline.
- **ADR 0021 made affinity path-sensitive and made array-valued fields
  borrowable places.** A move on a returning branch no longer kills the value on
  the fall-through path. This is exactly the control-flow precision resource
  values will need.

The old statement that unsafe Sable is blocked on all of “class values slice B”
is therefore obsolete. The remaining ordinary-class gaps — general `&mut C`,
local-to-local class moves, generic class-valued fields, and arbitrary nested
place syntax — are useful infrastructure, but they do not block the Lean probe
or a byte-only resource prototype.

They do reveal one constraint: the current `VarInfo.moved` bit is enough for
whole local class values, not for a mature resource system. Resource work should
build a real place-based affine engine and then reuse it for the remaining class
features, rather than extending the current special cases indefinitely.

## Decision in one paragraph

Unsafe Sable is a **verified resource sublanguage**, not a mode that turns
verification off.

> A raw pointer says **where**.  
> A resource says **what authority the program owns and what state it is in**.  
> A contract says **how an operation transforms that authority and state**.  
> `unsafe` makes low-level operations available; it grants no facts and waives
> no obligations.  
> Machine intrinsics are defined by the selected formal machine model.  
> `extern` contracts and explicit `assume`s are where environmental trust enters.

A package may contain arbitrary amounts of unsafe code and remain fully
verified, provided every obligation is proved and it depends on no unproved
external contracts. Unsafe is an audit surface, not by itself a trust gap.

## What realistic systems examples force

The design is judged against examples, not against the desire to resemble C or
Rust.

### Raw buffer manipulation

Implement safe operations such as copying between disjoint buffers by exposing
their storage temporarily. This forces raw pointers, byte ownership,
initialization state, provenance, bounds, nonescape, and reconstruction of safe
values. It is the smallest useful vertical slice.

### Foreign calls

Call a C ABI function that fills or reads a buffer. This forces ABI lowering,
erasure of proof-only authority, a trusted contract for code Sable cannot see,
explicit treatment of global effects, and a transitive trust manifest.

### An arena and a free-list allocator

Carve a root byte region into disjoint blocks, transfer blocks to clients, take
them back, and reuse their bytes. This forces split and join of ownership,
alignment, initialization, typed storage, root deallocation authority, and
allocator-specific block-return authority.

### An intrusive linked structure

Store raw links in nodes while one aggregate resource owns all node permissions.
This forces a dynamic number of resources, sealed extraction and reinsertion,
and a convincing answer to whether users can avoid writing separation logic.

### MMIO and privileged operations

A UART register, page-table instruction, or TLB invalidation is an interaction
with a device or architecture state machine, not an ordinary heap cell. This
forces trace semantics, environmental inputs, and profile-specific
capabilities.

### Concurrency

A spinlock forces atomics and interference. The current SVM is sequential;
`unsafe` cannot paper over that. Concurrency remains a separate machine-model
extension. The first concurrent benchmark should still be an SPSC queue, not a
spinlock smuggled into the sequential model.

### What does *not* force unsafe

Parsing bytes into a packet header can already be safe Sable: indexing,
arithmetic, and a ghost representation relation. A zero-copy lowering may be a
backend optimization. Pointer casting is not automatically a language feature
merely because C uses it.

## Three boundary categories

The design must keep three different things separate.

### Verified unsafe code

Code inside `unsafe { ... }` may invoke raw-memory, representation-changing,
foreign-boundary, or device operations. It remains typechecked and verified in
exactly the ordinary sense. Failed preconditions are failed VCs; resource misuse
is a checker error.

### Machine intrinsics

An `unsafe intrinsic` is part of a selected machine profile. Its behavior is
specified by the SVM or another formal machine model. It is an axiom of that
model in the same sense that fixed-width addition and allocation capacity
already are; it is not an ad hoc assumption made by the program.

Examples are raw byte loads and stores, root allocation, an MMIO write under a
particular device model, or an ISA instruction under a Sail profile.

### External contracts

An `extern` declaration describes an implementation outside the verified
module. Unless accompanied by an imported proof, its contract is an audited
environmental assumption. It must carry a stable audit identifier and appears
in every dependent export's trust manifest.

An explicit `assume` remains a separate source-level axiom. `unsafe` never
implicitly introduces one.

## The third value category

Sable gains three categories of values:

```text
program value    runtime; affine according to ordinary ownership
ghost value      erased; freely duplicable
resource value   erased; affine
```

Here **affine** means “usable at most once as owned authority.” A resource may be
moved, borrowed, transformed, or abandoned, but not copied. Abandoning a memory
resource may leak memory; it does not create use-after-free or double ownership.
A later `#[must_consume]` or linear-resource refinement may diagnose leaks, but
memory safety must not depend on it.

Lexical exposure tokens are deliberately stricter: the enclosing construct
requires the complete loan resource back before the scope may close.

## Authority, pure views, and the metatheory

The earlier sketch's slogan that “affinity and provability never meet” was too
strong. The precise split is:

> **Authority is a checker property. Resource state is a Lean value. The
> resource-soundness theorem connects them.**

The checker maintains an affine resource context

```text
Delta = r1 : R1, ..., rn : Rn
```

containing the live, uncopyable authorities. Lean does **not** receive those
authorities as duplicable propositions. For each live resource it receives only
an ordinary pure **view** describing facts such as:

```text
span.ptr
span.len
span.bytes
cell.ptr
cell.state
lease.allocator
```

Facts about a view may be copied and reused freely. Copying knowledge that a
cell is initialized does not copy the authority to access it.

A resource operation therefore has two coordinated meanings:

1. an affine typing rule that consumes, borrows, or produces actual resource
   tokens; and
2. a Lean contract relating the pure input and output views.

The eventual metatheory interprets the complete affine context over the raw
heap:

```text
Own(rawHeap, Delta)
```

and proves that every well-typed resource transformation preserves this
interpretation. Internally that interpretation may use separating conjunction
or a resource algebra. Users do not write it in ordinary contracts.

This division is important for Sable's architecture. The Rust compiler does not
parse Lean expressions and should not attempt to reject repeated occurrences of
`span` on `///` lines. It rejects repeated *consuming program uses* of the
resource token. Lean may mention the corresponding pure view as often as the
proof requires.

## Provisional source surface

The exact spelling should be allowed to change during the prototype. The
following is intended to make the static categories explicit, not to freeze the
grammar.

```sable
resource RawSpan mem;
resource PointsTo<u32> cell;

unsafe intrinsic fn load8(
    raw<u8> p,
    resource &RawSpan mem
) -> u8;

unsafe intrinsic fn store8(
    raw<u8> p,
    u8 value,
    resource &mut RawSpan mem
);

fn split_off(
    resource &mut RawSpan whole,
    u64 left_len
) -> resource RawSpan;
```

Resource declarations are program-language syntax because the Rust-side checker
must see them. They must not be encoded as `/// resource ...` proof lines.

The proof language sees the view associated with each resource name:

```sable
/// pre  mem.ptr = p
/// pre  mem.bytes.get 0 = ByteState.init expected
/// post result = expected
unsafe intrinsic fn load8(...);
```

Resource arguments and fields are erased from the ABI and runtime layout.

For the first prototype, resource types should be compiler/prelude-defined.
User-defined `resource type` declarations can wait until the memory core is
stable. When they arrive, they must have no ordinary public constructor: a
program may not fabricate authority by constructing a view-shaped value.

## Resource typing rules

### Moves

Passing a resource by value or returning it consumes the source place. Any later
owned use is `resource.use_after_move`.

### Shared borrows

`resource &R` permits read-only use of the authority and view. Any number of
shared borrows may coexist. The owner is frozen until they end.

### Mutable borrows

`resource &mut R` is unique and permits a function to return an updated view for
the same authority. No shared or second mutable borrow may overlap it.

The first resource implementation may add mutable resource borrows before
ordinary `&mut C`; both should ultimately share the same place/borrow engine.

### Branches

All fall-through branches must have the same **resource shape**: the same live
resource identities and types, with compatible borrow state. Their pure views
may differ and are merged in VC generation just as ordinary symbolic values
are.

A branch that returns contributes no state, matching ADR 0021's current
path-sensitive move rule.

### Loops

The live resource shape at every backedge must equal the shape at the loop head.
Views may change and are described by loop invariants. Creating one resource per
iteration without consuming or reintegrating it is rejected.

The first slice should reject outstanding resource borrows across a backedge.
This can be relaxed later if a benchmark requires it.

**Framing is not new machinery.** A resource untouched by the loop body keeps
its view facts for free: vcgen's havoc set is built by `collect_assigned` plus
`collect_mut_borrows` (`vcgen.rs`), and a `resource &mut R` argument lands in
the latter exactly as `&mut [T]` does today. So "unchanged resources are framed,
mutated ones are restated as invariants" falls out of the existing loop rule.
The genuine design question is narrower: a `resource &mut` in a loop body must
havoc the resource's **view**, never its **token identity** — the token is what
the shape check preserves across the backedge, and confusing the two would make
every loop drop the authority it is carrying.

**Backedge shape preservation is a metatheorem obligation, not only a checker
rule.** `Own(rawHeap, Delta)` is never a hypothesis in a generated VC. At a loop
head, havoc discards facts and re-establishes only the invariants — so nothing
in the goal says that two live tokens still describe *disjoint* authority on the
second iteration. That has to follow from shape equality at the backedge
preserving the interpretation. The resource-soundness theorem therefore needs a
loop case, proved in U1 alongside split and join. Without it, the loop rule is
the one place where "authority is a checker property" is asserted rather than
shown.

### Drops

Dropping an affine resource discards authority and may leak the underlying
external resource. It cannot make another token appear. The compiler should
warn for selected resource kinds, but soundness should not depend on mandatory
cleanup.

### Destruction semantics — an unbuilt prerequisite, stated

"A class destructor may consume resource fields" describes a Sable that does
not exist: `deinit` bodies must currently be empty (`check.rs`,
`type.deinit_body`, "owned fields are freed automatically"). Resource-owning
RAII classes need that lifted, and the semantics pinned before they are:

- `deinit` begins with exclusive ownership of `self`;
- the class invariant holds on entry (design §7) and need **not** be
  re-established — the value ceases to exist;
- the body may move or consume fields;
- moved fields are not dropped again; the rest drop in reverse declaration
  order;
- a `#[must_consume]` resource field must be consumed by the body or by its own
  destructor;
- an ordinary affine field may be abandoned, possibly with a leak warning.

This interacts with the place engine through `partially-moved`, and with the
interpreter: `interp.rs` checks the class invariant dynamically at every RAII
drop, which is unambiguous only because bodies are empty today. Once bodies run,
the order must be **check invariant → run body → drop remaining fields**, with
moved fields skipped — otherwise the monitor evaluates an invariant over a hole
the body just made. Erased resource fields are free (they do not exist at
runtime); moved-out *class* fields are exactly the case that bites.

Consequence for sequencing: RAII resource classes are U7a work, and U6's first
non-memory resource should pass its handle explicitly instead
(`fn close(i32 fd, resource OpenFile open)`), which needs none of this.

## Places: the checker work actually required

ADR 0020/0021 validated the direction but did not finish the infrastructure.
The resource checker should introduce a real `Place` representation rather than
adding more `String + optional field` cases.

A first version needs:

```text
Place := local | self | Place.field
```

with room for later projections. Resource array-element moves and arbitrary
pointer-derived places are out of scope.

The checker state should distinguish at least:

```text
live
moved
shared-borrowed(count)
mutably-borrowed
partially-moved        -- needed once resource fields may move independently
```

Resource identity must not be confused with its current Lean view symbol. A
mutable operation preserves or transforms the authority while producing a fresh
view version.

This place engine should be shared with ordinary affine class values, and built
against them **first** (U2a): ordinary classes give it a safe-side test surface
with an existing corpus, before erasure and view-versioning complicate the
picture. Local-to-local moves and general `&mut C` land there, not as a second
ownership system bolted on later.

A product type is not a prerequisite for the first resource slice. Prefer an
operation such as:

```sable
fn split_off(resource &mut RawSpan whole, u64 left_len)
    -> resource RawSpan;
```

which leaves one side in `whole` and returns the other.

## Core resource views

### Byte state

Raw allocator storage is not initially a `seq u8`. The model must distinguish
uninitialized bytes:

```text
ByteState := uninit | init(u8)
```

A span's pure view is approximately:

```text
RawSpanView = {
    allocation : AllocId,
    offset     : int,
    len        : int,
    bytes      : seq ByteState
}
```

The exact Lean structure may use naturals for sizes internally, but it should
remain pleasant against Sable's existing integer-lifted clauses.

### Typed cells

Typed storage uses a genuine state datatype:

```text
CellState<T> := uninit | init(T)

PointsToView<T> = {
    allocation : AllocId,
    offset     : int,
    state      : CellState<T>
}
```

Do not encode this as `option<T>`: an initialized `option<U>` whose value is
`none` must remain distinguishable from uninitialized storage.

### Root deallocation authority

```text
SystemDeallocView = {
    allocation : AllocId,
    size       : int,
    align      : int
}
```

It authorizes releasing the whole root allocation. Splitting a `RawSpan` never
splits or duplicates this token.

**External precedent.** Verus's `vstd::raw_ptr` library independently arrives
at nearly this factoring: separate permissions for typed and raw memory access
(`PointsTo`, `PointsToRaw`), initialization state carried in the permission
rather than the pointer, a distinct deallocation permission, and an allocation
operation that returns memory authority and deallocation authority as two
values. It also keeps mutability out of the raw pointer and provenance separate
from the numeric address. This is corroboration, not proof — but two designs
reaching the same split from different starting points is evidence the split is
forced by the problem rather than chosen by taste.

### Allocator block leases

A suballocation returned by a free-list allocator must not receive a system
free token. It receives an allocator-specific lease:

```text
BlockLeaseView = {
    allocator : AllocatorId,
    allocation : AllocId,
    offset : int,
    len : int
}
```

Calling the allocator's `free` consumes the lease and returns the region to the
allocator resource. The allocator retains the root `SystemDealloc` authority.

## Primitive resource transformations

The initial sealed transformations should be few and explicit.

### `split_off`

Consumes a mutable borrow of one `RawSpan`, proves `0 <= n <= len`, leaves the
prefix in the original token, and returns a token for the suffix. The views state
that the two byte sequences concatenate to the old sequence and share the same
allocation with adjacent offsets.

### `join`

Consumes two spans. Lean proves that they belong to the same allocation and are
adjacent in the required order. The result owns their concatenation.

Nonadjacency is a failed VC, not a checker error.

### `load8`

Requires a shared span resource, a pointer/range proof, and an initialized byte.
It returns the byte and leaves the resource view unchanged.

### `store8`

Requires a mutable span resource and a pointer/range proof. It changes the
selected byte to `init(value)`.

### `take8`

Returns an initialized byte and changes it to `uninit`. Reading it again is a
failed initialization VC unless it is reinitialized.

### `copy_nonoverlapping`

Takes a shared source resource and a distinct mutable destination resource. The
affine interpretation supplies separation; contracts state bounds and the
resulting bytes. If source and destination are subranges of one allocation, the
caller must split the resource first.

This is an important design test: users should not have to prove a general heap
nonoverlap formula merely because they already possess two exclusive resource
tokens.

## Aggregate resources

A dynamic collection of permissions cannot be represented by a pure Lean map
alone. The correct design is:

```text
one affine ResourceMap<K, R> token
+ one pure Lean map<K, View<R>> view
+ sealed take/put/borrow operations
```

The hidden interpretation of `ResourceMap<K,R>` is the valid composition of all
contained `R` resources. Its disjointness does **not** follow merely from the
pure map being a function.

Operations:

- `take(key)` consumes the aggregate temporarily and returns one contained
  resource plus the residual aggregate, or mutates the aggregate and returns
  the resource;
- `put(key, resource)` reinserts authority, proving the key is absent and the
  view is updated;
- `borrow(key)` and `borrow_mut(key)` provide tracked entry borrows without a
  noisy remove/reinsert cycle.

The intrusive-list benchmark is the acceptance test. If its proof becomes a
wall of explicit resource rearrangement, improve these sealed operations before
adding a user-visible separation logic.

## Raw pointers

The surface type is:

```sable
raw<T>
```

A raw pointer carries no ownership and is copyable. Operationally it contains
provenance plus an offset; the static `T` describes the intended access type.
Creating or copying a pointer never creates a resource.

### v1 rules

- no general integer-to-pointer conversion;
- pointer arithmetic preserves provenance;
- forming a pointer within a span permits the one-past endpoint, but
  dereferencing requires the whole accessed range inside the allocation;
- pointer subtraction and ordering require common provenance;
- equality is available only when both pointers are known live; for live
  allocations it agrees with machine-address equality;
- comparisons involving dangling pointers are excluded from v1;
- null is represented by `option<raw<T>>`;
- changing `raw<u8>` to `raw<T>` requires alignment, sufficient extent, and an
  accompanying resource transformation;
- a pointer alone never licenses a load, store, cast, or free.

The exact equality rule should be tested against the intrusive-list design. A
first implementation may restrict the list to nodes carved from one arena,
which keeps every compared pointer under one provenance.

## The raw SVM heap

The current SVM keeps owned arrays and classes in the value world. Unsafe Sable
should not replace that model. It adds a separate raw heap:

```text
Config = continuation × frames × locals × rawHeap × ...
```

Every existing safe rule preserves `rawHeap` unchanged.

A byte-only first heap contains:

```text
RawPtr     = allocation id × byte offset
Allocation = size × alignment × liveness × seq ByteState
RawHeap    = finite map AllocId Allocation
```

A deterministic `nextAlloc` counter supplies fresh provenance. Deallocation
marks or removes the allocation so stale provenance can never authorize a later
allocation.

Invalid raw operations reach the SVM's explicit `undef` terminal outcome;
verified code proves them unreachable. The reference interpreter may report a
precise dynamic diagnostic while preserving the same semantic classification.

Resources do not appear in the machine configuration. They are erased static
authority. The resource-soundness theorem connects the checker context to the
heap.

The raw-heap extension must update all existing semantic-oracle artifacts:

- relational rules in `lean/Sable/SVM.lean`;
- functional evaluator and agreement proofs in `lean/Sable/SVMEval.lean`;
- determinism, totality, and progress corollaries;
- Rust lowering in `compiler/src/svm.rs`;
- differential subjects in `corpus/svm-diff`.

Unsupported raw operations in the differential harness remain hard failures,
not silent skips.

## Lexical exposure of safe arrays

The first bridge from safe values to raw memory is byte-only lexical exposure:

```sable
unsafe expose &mut dst as (
    raw<u8> p,
    resource RawSpan mem
) {
    ...
}
```

A shared form exposes `&src` read-only.

### Static meaning

The construct creates a hidden generative **loan brand**. The pointer and
resource are parameterized by that brand internally, although users write no
lifetime syntax. Values carrying the brand cannot be returned, assigned to an
outer place, or stored in longer-lived data.

At scope exit:

- the complete original extent must again be owned;
- every byte needed to reconstruct the safe array must be initialized;
- no pointer or derived resource with the loan brand may escape;
- mutable exposure reconstructs the array from the final bytes;
- shared exposure proves the bytes unchanged.

The first version should require explicit joining of split descendants before
exit rather than trying to normalize arbitrary resource partitions.

### Semantic meaning

The SVM may model exposure by creating a fresh loan allocation containing the
array bytes, executing the body, then copying the final bytes back and removing
the allocation. A native backend may compile the same construct to taking the
address of the existing buffer. Nonescape makes these implementations
observationally equivalent for the permitted operations.

## The first safe wrapper

The first end-to-end subject should be deliberately small:

```sable
/// pre  src.len <= dst.len
/// post forall i, 0 <= i -> i < src.len ->
///          dst.get i = old src.get i
/// post forall i, src.len <= i -> i < dst.len ->
///          dst.get i = old dst.get i
fn copy_prefix(&[u8] src, &mut [u8] dst) {
    unsafe expose &src as (sp, resource smem) {
        unsafe expose &mut dst as (dp, resource dmem) {
            raw_copy_nonoverlapping(
                sp, dp, src.len,
                resource &smem,
                resource &mut dmem
            );
        }
    }
}
```

The spelling is provisional. The acceptance criterion is not.

The function must verify with a short value-level contract and no user-visible
heap predicate, frame clause, separating conjunction, provenance lemma, or
manual proof of global disjointness.

## Typed storage without premature byte reinterpretation

Placing a typed value into raw storage and interpreting arbitrary bytes as a
value are different powers and should remain separate.

### Abstract typed storage

For `PointsTo<T>`, the SVM may initially model an occupied extent as an abstract
typed object containing a `T` value and a layout. It need not expose the byte
encoding of `T`.

Conceptually, an allocation is partitioned into extents that are either:

```text
raw bytes: seq ByteState
typed object: type tag × value × size × alignment
```

`init<T>` converts a sufficiently large, aligned uninitialized byte extent into
an initialized typed object. `take<T>` removes the value and returns
uninitialized storage. Byte access to a typed extent is invalid unless an
explicit representation operation is available.

This permits typed cells containing raw pointers or structured records without
first solving provenance-preserving serialization.

### Layout concepts

The minimum concept is about size and alignment, not byte representation:

```text
Layout<T>
    size_of<T>  : nat
    align_of<T> : nat
    laws: alignment is nonzero and a power of two
```

Stronger capabilities are separate law-carrying concepts:

```text
RawStorable<T>      may inhabit an abstract typed raw extent
BitwiseRepr<T>      has an explicit byte representation relation
BitwiseCopyable<T>  may be copied as bytes
FromBytes<T>        selected byte sequences decode as T
Zeroable<T>         all-zero bytes represent a valid T
CRepr<T>            layout and representation match a declared C ABI
```

The first typed slice should support fixed-width integers and explicitly laid
out POD records. Arbitrary classes, references, destructor-bearing values,
unions, and packed records remain out of scope.

Alignment enters as soon as raw storage becomes typed. It is part of the first
typed-memory model, not merely a backend concern.

## Allocation authority

No allocator manufactures ownership from nothing. Every allocator refines and
transfers a root capability obtained from one of a few modelled sources:

- an SVM `system_alloc` intrinsic;
- a statically declared freestanding region;
- a platform profile's boot-memory description;
- an audited foreign operation such as `mmap`.

A root allocation result is conceptually:

```sable
class RawAllocation {
    raw<u8> base;
    u64 len;
    resource RawSpan bytes;
    resource SystemDealloc release;
}
```

The resource fields erase at runtime.

### Static bump arena

The first allocator uses a program-lifetime static region, avoiding the
question of whether returned blocks outlive their arena.

Its invariant is the value-level image of:

```text
allocated prefix + unused suffix = original region
```

Allocation aligns the cursor, splits off padding, splits off the requested
extent, and initializes it if a typed result is requested.

Most of the arena should be ordinary verified code invoking safe resource
transformations. If the whole allocator must sit inside one large unsafe block,
the resource API is too weak.

### In-band free-list allocator

The next allocator stores free-list metadata inside free blocks. This is the
forcing example because bytes change roles among:

- allocator metadata;
- uninitialized client storage;
- initialized typed values.

The allocator resource must express:

```text
free regions are pairwise disjoint
live leased regions are pairwise disjoint
free and live regions are disjoint
free union live covers the root allocation
free-list links describe exactly the free regions
```

Allocation consumes a free region and returns a `BlockLease`. Deallocation
consumes that lease and reinserts the region. Coalescing joins adjacent span
resources.

## Foreign-function interfaces

FFI should land early, but the first subject should be deterministic.

### First extern benchmark

Use a tiny C-style shim such as:

```text
fill(ptr, len, byte)
checksum(ptr, len)
copy(dst, src, len)
```

This isolates ABI lowering, noescape, buffer mutation, resource erasure, trusted
contracts, and the manifest. A real `read(2)` adds file state, environmental
input, short reads, errors, and interruption; it should be the second FFI
benchmark.

### Resource-typed effects, not arbitrary frame formulas

An extern declaration should state effects structurally through its resource
parameters:

```sable
extern "C" #[audit(id := "test.fill.v1", reason := "test shim")]
fn c_fill(
    raw<u8> p,
    u64 n,
    u8 value,
    resource &mut RawSpan mem
);
```

Only passed mutable resources may change; all other resources are framed by the
caller-side ownership discipline. If the foreign operation changes global
state, it must receive an explicit world capability such as
`resource &mut PosixWorld`.

The foreign implementation is trusted to respect this ownership-shaped
contract, but callers do not need a free-form global `modifies` clause.

Resource arguments are erased from the ABI. The C function receives the
runtime pointer, length, and byte value only.

### Nonescape by default

Foreign pointer arguments are `noescape` unless explicitly declared otherwise.
This allows a safe slice to be exposed for the duration of the call and closed
immediately afterward.

Retained pointers, callbacks, and ownership transfer to foreign code are out of
scope for v1.

### POSIX-shaped follow-up

After the deterministic shim, add:

```text
open / read / write / close
```

with an affine `OpenFile` resource. `close` consumes it. File position and
external I/O behavior live in an explicit `PosixWorld` resource and scripted
world model for tests.

## Trust manifests and build status

Separate verification already gives Sable content-addressed module artifacts.
Unsafe/FFI metadata should travel with those artifacts.

Each verified module should emit a manifest containing:

- selected machine profile and profile hash;
- machine intrinsics used;
- audited extern contracts used;
- explicit source `assume`s;
- deferred obligations;
- unsafe blocks and source spans;
- public interfaces exposing raw or resource types.

**The manifest is hashed into the artifact, not stored beside it.** ADR 0018's
artifact hash is `fnv64(prelude_hash, generated_lean_content)` — a manifest is
not generated Lean, so the two statements "stored beside the artifact" and
"included in the hash" are a real fork, and the second is correct: an
artifact's validity is mere existence of its `.ok` file, so an artifact must not
survive a change to what it trusted. Changing an audit id, adding an intrinsic,
or introducing an `assume` has to invalidate the artifact exactly as changing a
proof does. Concretely, U5 emits the manifest-relevant declarations into the
hashed content (a comment header is enough — the hash is over bytes), which
costs nothing and reuses the staleness machinery whole. Importers union
dependency manifests. A later refinement can slice the manifest per export
using the call graph; module-level transitive manifests are sufficient for the
prototype.

Suggested status language:

```text
status: fully verified
unsafe blocks:       14  (all obligations proved)
machine intrinsics:   4  (SVM profile: raw-memory-v1)
extern assumptions:   0
source assumes:       0
defers:               0
```

or:

```text
status: verified relative to audited boundary
extern assumptions: 2
  - posix.read.v1
  - posix.write.v1
```

Do not print `fully verified` when unproved extern contracts remain. Machine
intrinsics defined by the selected formal profile are part of the declared axiom
base, not hidden source assumptions.

## What `unsafe {}` means

`unsafe {}` is worth retaining because it grants access to the low-level
operational vocabulary:

- raw loads and stores;
- typed/raw representation changes;
- deallocation;
- foreign calls;
- MMIO and privileged intrinsics.

It does **not**:

- make a false proposition true;
- suppress a VC;
- fabricate a resource;
- permit duplicate authority;
- change an invalid operation into unchecked native behavior;
- make `assume` implicit.

Pure pointer arithmetic and safe resource transformations such as split and join
need not require an unsafe block if their contracts are fully checked.

The first version need not add `unsafe fn`. Tooling can derive “unsafe
interface” from a public signature containing raw/resource types. Add an
explicit function marker later only if a forcing example shows that call-site
propagation is useful.

The compiler should reject unsafe operations outside a block and warn about an
empty or unnecessary unsafe block.

**This much is settled: `unsafe` grants no logical authority and waives no
obligation.** Whether the *lexical marker* earns its syntactic weight is not
settled, and the sketch's counterargument stands: a marker that confers nothing
is a lint, and lints should be derived so they cannot lie. The position here —
keep the block, because it does grant something operational (access to a
restricted vocabulary), while deriving everything that could otherwise go stale
(unsafe interfaces from signatures, trust dependencies from the call graph and
manifests, unnecessary blocks from the operations inside them) — is
**provisional through U5**. Revisit it once `copy_prefix`, the extern shim, and
the arena exist and there is evidence rather than taste.

## MMIO, devices, and privileged state

A device register is not a `PointsTo<u32>` plus a volatile bit.

A machine profile should provide capabilities such as:

```text
MmioRegion<Device>
PrivilegedCpu<State>
```

and intrinsics whose semantics update an explicit environment state and append
observable events to a trace.

Device reads consume values from an input oracle supplied as part of the
machine configuration. Parameterizing the machine by an oracle preserves
determinism in the same way the existing allocation-capacity parameter does.
Correctness quantifies over admissible oracles.

Driver specifications should normally use trace projections:

```text
uartWrites(trace, UART0) = expectedBytes
```

rather than expose the complete global event list in every contract.

A fixed-address UART capability comes from a platform profile or audited boot
fact, not from a general integer-to-pointer cast.

Page-table writes, TLB invalidation, interrupt masking, and similar operations
follow the same pattern against a formal ISA/profile model.

## Monitorability and testing

The compile-time, proof-time, and runtime failure classes should remain
separate.

### Checker diagnostics

Examples:

```text
resource.use_after_move
resource.borrow_conflict
resource.branch_shape_mismatch
resource.loop_shape_mismatch
resource.escape
raw.unsafe_required
```

These cover duplicate/consumed authority, illegal borrows, mismatched resource
contexts, and lexical loan escape.

### Verification failures

Examples:

```text
raw pointer outside owned span
uninitialized read
misaligned typed conversion
nonadjacent join
copy range exceeds source or destination
wrong allocation or allocator identity
```

These are mathematical preconditions over resource views and therefore named
VCs, not typechecker errors.

### Dynamic/SVM failures

The shadow raw heap can detect:

```text
out-of-bounds access
uninitialized read
use after free
double free
type confusion
overlapping copy_nonoverlapping
```

A source program rejected for duplicating a resource cannot be executed by
`sable test`; it belongs in `corpus/must-fail`. Invalid lowered SVM subjects can
still test that bypassed checks reach the intended `undef` outcome.

### `defer`

For unsafe v1, resource/provenance/liveness/initialization obligations are not
deferable. A sanitizer interpreter may monitor them using shadow metadata, but
native release code is not required to carry that metadata.

Sanitizer-detectable is not the same as release-monitorable.

## Implementation ladder

Use `U0`, `U1`, ... here so the plan does not guess future global milestone
numbers.

Three kinds of dependency run through it, and they are worth keeping apart:

```text
semantic       U1 decides the resource model everything else encodes
implementation U2a's place engine is what U2b's resource checking runs on
benchmark      U4's copy_prefix judges whether the abstraction is usable
```

Only the second is a build-order constraint. U1 is unblocked today; U4 is a
go/no-go, not a prerequisite for having built U1–U3.

### U0 — prerequisite audit *(mostly complete)*

Already landed:

- class-valued fields;
- by-value affine class parameters;
- field borrows;
- array-valued field borrows;
- path-sensitive move joins;
- SVM calls/frames and the semantic oracle;
- separate, content-addressed module verification.

Still needed, and now scheduled rather than open-ended — a general place
representation, local-to-local moves, general `&mut C`, and resource mutable
borrows are U2a/U2b; partial moves and resource fields are U7a; nested
program-side place syntax stays deferred until something forces it.

None of it blocks U1. The Lean probe has no compiler dependency at all: the Rust
side owns program-language flow facts, and Lean receives proof expressions
verbatim, so the probe can be written and judged before a line of checker code
exists.

### U1 — concrete Lean resource probe *(first pass done 2026-08-11)*

`docs/notes/unsafe-probe.lean` exists and checks: the byte model, the context
interpretation, preservation for split/join/load/store/take/allocate/free, the
aggregate round trip, and the carving loop including interpretation preservation
across the backedge. Five vcgen-shaped goals close under `sable_auto` at the
default budget; `#print axioms` shows no `sorryAx`. Question 5 (abstract typed
storage) is **not** covered — the probe is byte-only, and the findings section
says what that would take. Remaining before U2: the ADR.

Create `docs/notes/unsafe-probe.lean`, matching the convention every prior probe
used (`bignum-probe`, `algd-probe`, `json-probe`, `utf8-probe`); it graduates
into `lean/Sable/` only once an ADR adopts it.

Develop it against the real prelude at the **production grind budget** (ADR
0011, `sable.grindHeartbeats` default 50000). Every probe that transferred
cleanly was measured against the automation that would actually run it; a
resource model that closes under an unbounded budget but not under the budget
is a false positive on this milestone's central question.

Do **not** begin with a generic separation-logic library. Define one concrete
model:

```text
AllocId
RawPtr
ByteState
RawHeap
RawSpanView
SystemDeallocView
```

Define an affine-context interpretation and prove preservation for:

```text
split_off
join
load8
store8
take8
allocate
free
```

Then add a small aggregate-resource model with a pure map view and prove sealed
`take`, `put`, and borrow operations preserve its interpretation.

Questions U1 must answer:

1. Are the pure view contracts concise and automation-friendly?
2. Can the hidden interpretation establish separation without exposing `*` in
   user clauses?
3. Does the aggregate-resource design work for more than a hand-picked finite
   list?
4. Which facts must be maintained by the checker rather than proved per call?
5. Does abstract typed storage avoid premature byte-representation machinery?
6. Can a loop whose resource *shape* is fixed but whose *views* change be
   verified with ordinary value-level invariants, without restating hidden
   separation facts — and does shape equality at the backedge preserve the
   context interpretation?

Question 6 needs a concrete subject, not isolated split/join theorems. Use a
carving loop over two live tokens:

```text
processed : RawSpan
remaining : RawSpan
```

Each iteration splits one byte off `remaining`, transforms it, and joins it onto
`processed`. The value-level invariant is the pleasant part —

```text
processed.bytes ++ remaining.bytes = original.bytes
processed and remaining are adjacent in one allocation
processed.len + remaining.len = original.len
```

— and the interesting part is that nothing in that invariant says the two
tokens are disjoint. That must come from the interpretation surviving the
backedge.

Exit criteria:

- no `sorry` in the accepted probe;
- split/join/load/store preservation theorems proved;
- one aggregate `take`/`put` round trip proved;
- the carving loop proved, including **interpretation** preservation across the
  backedge, not only view preservation;
- representative generated-style VCs close under `sable_auto` at the default
  heartbeat budget, or under short explicit Lean proofs;
- an ADR records the chosen interpretation before compiler implementation.

### U2 — the place-based ownership engine, then the resource category

One engine, two consumers, landed in this order so the ownership machinery is
exercised on ordinary values before erasure and view-versioning are layered on
top. `VarInfo { initialized, mutable, moved }` is a bit-set adequate for whole
local class values; it is not an engine, and resource work should not extend it
further.

#### U2a — general place/borrow engine (safe side) *(done 2026-08-11)*

The safe-side test surface paid before the engine was even finished, and kept
paying. Building `Place` (root plus field path) and asking what it would catch
turned up **three** holes, all now closed with guards:

- a mutable borrow overlapping another borrow in the same call was **unsound**
  (vcgen havocs the mutable argument and keeps the shared argument's pre-call
  symbol — a verified program returned the wrong answer and the monitor caught
  it);
- a borrow of a moved-out place was accepted, because `use_after_move` only
  guarded the name-read path, not the borrow path. Latent rather than live today
  — the interpreter shares `Rc`s, so nothing is destroyed at a move — and
  unsound the moment a move actually transfers, which is what resources do;
- a `&mut self` method call in a *declaration initializer* did not put its
  receiver in the loop's havoc set, and `Stmt::VarDecl` initializers were not
  scanned at all. `while (...) { u64 t = c.bump(); ... }` kept `c`'s pre-loop
  state at the loop head; `post result = 0` verified on a function returning 3.
  **Unsound**, and again caught by the monitor.

Two more came out of `&mut C` itself: class-borrow arguments on *methods* were
accepted by the checker and hit an `unreachable!` in vcgen (an ICE reachable
from ordinary source, `&C` included), and construction assumed a borrowed
argument's class invariant without owing `borrow_inv` for it — the one call form
that skipped ADR 0010's obligation. This is the argument for U2a in one section.

What landed:

- a reusable `Place` (root plus field path, with `contains`/`overlaps`), keying
  a move set on `Ctx` — the ad hoc `VarInfo.moved` bit is gone;
- branch joins over that state (ADR 0021's rule generalized: a returning branch
  reaches nothing);
- local-to-local class moves (`a = b;`, `var d = a;`), including reviving a
  moved-from local by moving a new value in;
- general `&mut C` on functions, methods, and inits, with ADR 0023 fixing what
  it means: mutation only through the class's own `&mut self` methods, which is
  what makes the caller's post-call invariant assumption sound;
- one entry-state map (`entry_states`) shared by `&mut [T]`, `&mut C`, and the
  `self` of a `&mut self` method, and one pair of helpers
  (`push_borrow_invs`, `havoc_mut_class_args`) shared by all three call forms;
- named diagnostics with spans for every rejection: `borrow.conflict`,
  `class.use_after_move`, `class.mut_field_borrow`, `type.mut_borrow_shared`,
  `mut.method_shared_borrow`, `mut.borrow_immutable`, `type.class_arg_borrow`,
  `type.class_borrow_mutability`.

`&mut C` was the point of doing this first: a safe-side consumer with an existing
corpus to shake the engine out on, isolated from the raw-memory model. Nothing
forced it on its own — it was paying for a test surface, and three soundness bugs
is what the surface returned. `Integer::negate_in_place` is the first library
operation that mutates instead of allocating.

Deferred with reasons, not silence: mutable *field* borrows (`&mut a.f`), because
no party can re-establish the base object's invariant — the place machinery
supports the borrow, the invariant discipline does not (ADR 0023); and partial
moves out of fields, which stay U7a (`Ctx::is_partially_moved` exists and nothing
produces field moves yet).

The one piece of the sketched lattice that did **not** need building: per-place
`shared-borrowed(n) | mutably-borrowed` state. A borrow is an argument, not a
value — no borrow-typed locals, returns, or fields — so borrow state never has to
survive a statement, and overlap is decided within a single call. U2b should
check whether resources change that before adding the counters.

#### U2b — resource category on the same engine *(done 2026-08-11)*

The category exists, on U2a's engine and nothing else. ADR 0024 records the
decisions; the load-bearing one is that **the view is ghost** — a clause may say
`s.len`, program code may not. That single line is what makes erasure real
rather than aspirational: a program able to read the view would need it at
runtime, and a runtime view is a thing a program could construct, which is the
authority forgery the category exists to prevent.

Landed:

- `Ty::Res(k)` / `Ty::ResRef(k, m)`, spelled `resource RawSpan`,
  `resource &RawSpan`, `resource &mut RawSpan`, at parameters, returns, and
  locals — the category written at every binding site, borrow marker inside it;
- `lean/Sable/Raw.lean`: `ByteState` and `SpanView` with `take`/`drop`/`cat`
  and their length and byte lemmas. The *views* graduate from the probe, as
  ADR 0022 said they would when the compiler emits against them; `Own`, `Cap`,
  and the preservation theorems stay in `unsafe-probe.lean` until raw operations
  exist to be justified;
- moves, borrows, borrow conflicts, and use-after-move: the same `Place` set and
  the same `check_borrow_conflicts` U2a built, plus a type test. No second
  ownership system, which was the exit criterion that mattered;
- shape checks at branch joins and loop backedges, *stricter* than the class
  rule: a resource moved on one reaching branch and not the other is rejected,
  and a loop body that consumes a resource live at the head is rejected. Not for
  soundness — dropping is permitted — but because with authority the difference
  between a deliberate release and a forgotten path is worth a diagnostic;
- view binders in Lean emission, versioned separately from token identity: the
  loop havocs the *view* and preserves the *token*, and the corpus subject
  demonstrates both halves (`framed_loop` verifies only with the view invariant;
  without it the post fails);
- erasure from interpreter call arguments and runtime parameter lists;
- eleven named diagnostics, each with a `must-fail` guard.

`resource &mut R` needed **no new vcgen machinery at all**: it is the `&mut`
array rule with a view instead of a sequence, so the `entry_states` map and
`havoc_mut_borrow_args` that U2a generalized already covered it. That is the
strongest evidence so far for the sketch's central claim — the logic does not
know resources are special, because in the logic they are not.

Still narrow, deliberately: built-in `RawSpan` only, no resource fields, no
user-defined resource types, no raw machine operations, no partial move from
class fields. Class members may not take resources at all
(`resource.in_class`) — authority inside a class needs destruction semantics,
an unbuilt prerequisite rather than a default to pick silently.

**One exit criterion is implemented but not demonstrated.** "Resource parameters
do not appear in interpreter/native runtime arguments" is true of the code —
both sides drop the same positions by the same filter — but no test reaches it,
because nothing can *create* a `RawSpan` yet. Allocation is U3. Recorded rather
than claimed.

`split_off` and `join` landed as compiler-known sealed transformations, not
library functions: each states a rule about who owns what, and those rules are
the compiler's. `split_off(&mut whole, n)` leaves the prefix in the borrowed
token and returns the suffix — **no product type was needed**, which was the
open question; one side goes back through the borrow. Bounds and adjacency are
*failed VCs, never checker errors*: the checker tracks tokens, not geometry, and
that division is the whole architecture in one rule.

The corpus subject that matters is `carve_one_at_a_time`: one byte carved off
the front per iteration and joined onto the processed prefix, two tokens live
across the backedge with both views changing every turn. That is the shape the
U1 probe's `own_carve_step` was proved for, now a verified program — 23
obligations, zero discharge scripts. It also found a hole in the loop-shape rule
as first written (a resource declared *and* consumed inside the body was flagged,
though it is per-iteration scratch the backedge does not owe) and a hole in
`join`'s argument handling: moving both arguments in a second pass accepts
`join(a, a)`, and the adjacency VC does **not** catch it, because an empty span
is adjacent to itself. A zero-length token duplicated out of nothing is exactly
the failure the category exists to prevent, and it survived about ten minutes.

### U3 — byte raw heap in the formal SVM *(done 2026-08-11, ADR 0025)*

The byte heap is in the normative machine: `RawHeap` (a fresh-provenance
counter plus a partial map of allocations, each a `Seq RawByte` where
uninitialized is a distinct state), `Val.ptr alloc off` — provenance plus an
offset, never an address — and the operations `rawAlloc`, `rawFree`, `rawLoad8`,
`rawStore8`, `rawTake8`, plus `ptrAdd`.

**The structural finding: pointer arithmetic is pure, so it is an expression,
and everything that touches the heap is a statement.** That is the
A-normalization precedent calls already set, and it is what let `Eval` stay
*completely* unchanged — expressions still have no heap, so not one existing
expression rule was reinterpreted. The claim that unsafe Sable extends the
machine rather than reinterpreting it is checked rather than asserted: the heap
was threaded through the configuration in its own commit, with no operations at
all, and agreement in both directions, determinism, totality, and progress
re-proved with no change to any tactic.

The rules state their side conditions as *decidable* predicates
(`RawHeap.loadByte`, `.freeable`, `.inBounds`) rather than existentials over the
heap. Written the other way first, the agreement proofs needed case analysis on
inaccessible implicit binders — but the real argument is normative: these are
exactly the questions the machine must compute to tell a store from `undef`.

`Sable/SVMRawTests.lean` holds 20 direct SVM subjects — programs in the
machine's own syntax, which is what this rung intended — pinning the valid path
and every route to `undef`: out of bounds either way, a load of never-written
storage, a load of a byte `take8` emptied (and that writing it back makes it
readable again), use after free, double free, interior free, a non-pointer
dereference, and an out-of-`u8` store. Allocation past the cap is `Trap.oom`,
because exhausting memory is a defined failure, not a program error.

**Two layers of defence, both verified by injection.** An evaluator that forgets
`take8`'s write-back fails the agreement proof. Changing the rule *and* the
evaluator together consistently passes agreement and fails an outcome guard.
Neither alone catches both — which is the argument for keeping the outcome
subjects rather than trusting agreement.

**Ordering correction, recorded rather than quietly satisfied.** Two exit
criteria as originally worded — "valid and invalid raw subjects added to
`corpus/svm-diff`" and "injected wrong lowering is detected" — presuppose a
*source surface* for the raw operations, which this rung explicitly does not
build ("no lexical exposure yet"). `corpus/svm-diff` subjects are `.sable` files
lowered by `svm.rs`; with no raw syntax there is nothing to lower and nothing
for `interp.rs` to run. Both move to U4, which is where the surface arrives.
What this rung could check in their place — that an injected wrong *semantics*
is detected — it checks twice.

Still open here: alignment (nothing in a byte-only heap can observe it; it
starts to matter with typed storage) and `copy_nonoverlapping` (it waits for the
operations to have contracts).

### U4 — lexical byte exposure and `copy_prefix` *(done 2026-08-11, ADR 0026)*

**The go/no-go verdict is go.** `copy_prefix` verifies from a three-line
value-level contract with no heap predicate, frame clause, separating
conjunction, provenance lemma, disjointness proof, or discharge script — and so
do four other subjects in `corpus/verifies/unsafe_copy.sable`, including one
that splits a span inside the exposure and rejoins it. 29 obligations, zero hand
proofs. The checkpoint's second half — "the checker can explain failures
locally" — is carried by eight negative subjects, each landing on a named
diagnostic at the right span.

Two decisions carry it:

- **Exposure is a construct, not a proof.** `unsafe expose &a as (p, resource m)
  { ... }` lends the array's bytes and takes them back; the bridge between the
  safe world and the raw world is syntax with generated obligations.
- **Affinity supplies separation.** `raw_copy_nonoverlapping` has *no nonoverlap
  premise*. The two spans are distinct affine tokens, and that is what being
  distinct means. This was the design test the plan named, and it passes.

Loan brands do nonescape without lifetime syntax: branded values cannot be
returned, assigned outside the body, or passed to a user function. The brand
follows *provenance* through `raw_offset`/`split_off`/`join` and **not** onto
loaded bytes — a byte read out of memory is an ordinary number, and branding it
made `return b` illegal until a corpus subject caught it.

The three findings that decided whether the rung passed are all about the shape
of what the *compiler* emits, which is the point: the vocabulary has to be
visible to `simp` (an `abbrev` is not — every notion carries an explicit
unfolding lemma); `reconstructible` had to lose its existential, because
`∃ b, get k = .init b ∧ ...` defeats `grind`; and a store's effect has to be
*functional* (`m₂ = write m k (.init w)`) rather than a conjunction of
"index k is now this, everything else unchanged", which left grind in case
analysis at every exit. Reconstructibility itself is tracked as a hypothesis
established by each operation — the treatment array length and element ranges
already get across a store — and one lemma per operation is the entire cost of
keeping the exit automatic.

`unsafe regions: N` appears in build output: the count of places resting on a
proof rather than the type system is a fact about the program.

**U3's two inherited criteria are now met**, since the raw operations finally
have a surface to lower: `svm.rs` expands exposure into the machine's own
loan-allocation model (allocate, copy in, run, copy back, release),
`corpus/svm-diff` gained a valid and an invalid raw subject, and an injected
wrong lowering diverges. The interpreter's raw failures classify as `undef`
while keeping a precise message — the licence ADR 0025 granted.

Two things recorded rather than hidden. **The exposure's exit obligation is
currently unfalsifiable**: every operation in this surface preserves
reconstructibility, so it always closes. `take8` is what will make it bite — it
is in the machine but not the surface, and needs a strengthened
`write_reconstructible`. So the plan's negative subject "read an uninitialized
byte" is unreachable for now; `load8_init`, a real obligation on every load, is
the guard that exists instead. And **a stale warm `sable daemon` serves the old
prelude after a `lake build`**, which cost real time here and will cost it
again.

### U5 — deterministic extern shim and trust manifest *(done 2026-08-11, ADR 0027)*

`extern "C" #[audit(id := "...", reason := "...")] fn c_fill(...);` — a foreign
declaration whose contract is *audited*, not proved. It owes no obligations
because there is no body to check it against, but its clauses still get
well-formedness defs: a trusted contract that does not elaborate is not a
contract. The metadata is mandatory, because a trusted contract with no recorded
reason is an unsourced axiom.

**The interesting part of this rung was not the calling convention, it was the
honesty of the output.** Build status now refuses to say `fully verified` when it
is trusting something:

```text
unsafe regions: 8
extern assumptions: 2
  - test.checksum.v1 (c_checksum): ...
  - test.fill.v1 (c_fill): ...
status: verified relative to audited boundary
```

The manifest goes **inside** the hashed content as a comment header, as this note
already argued it must: an artifact's validity is mere existence of its `.ok`
file, so it must not survive a change to what it trusted. Verified — `test.fill.v1`
and `test.fill.v2` hash differently. Imports need no union step, since the flat
merge already puts a dependency's externs in the importer's program, and an
importer's status names the boundary it inherited.

Effects are **structural**, through the resource parameters: only a passed
`resource &mut R` may change, a `resource &R` frames itself, and there is no
`modifies` clause in the language to get wrong. `checksum_all` proves its array
comes back byte for byte across a foreign call. Resources are erased from the ABI,
so the shim receives the pointer, the length, and the byte. An extern may not
return raw or resource storage and may not be generic — forbidding retention *in
the signature* is what makes handing borrowed storage to a foreign function safe
at all.

Three findings:

- **U4's brand rule was too blunt**, and this rung found it: it forbade passing
  branded storage to any function, which blocked the extern call outright. The
  right rule follows from a property of the language — with no globals and no raw-
  or resource-typed fields, a callee that cannot *return* storage cannot retain it
  either. Only a signature returning raw or resource launders a brand.
- **`extern.generic` had to move to the parser**: mono drops an uninstantiated
  template before the checker sees it and substitutes the parameters away on an
  instantiated one, so there is no generic extern left for a checker rule.
- **U4's unfalsifiable exposure obligation is now falsifiable.** Every operation
  in U4's surface preserved reconstructibility, so `expose.<a>.bytes` always
  closed; an extern whose post says the bytes become `uninit` fails it. Trusting a
  boundary is different from trusting the compiler, and this is where it shows.

Test shims are keyed on the **audit id**, not the name — the id names the contract
version the program was verified against. An unknown id traps rather than running
the empty body, because a contract that appears to hold because nothing happened
is the one outcome a monitor must never produce (`corpus/test-fails/extern_no_shim.sable`).

Still open: the rest of the manifest (machine profile and hash, intrinsics used,
per-export slicing — the profile has no selection mechanism yet, and slicing is
already marked optional for the prototype), and any real ABI. Nothing is compiled
or linked; what this rung establishes is the contract shape and the trust
bookkeeping.

### U6 — POSIX-shaped handles and scripted worlds *(done 2026-08-11, ADR 0028)*

Two non-memory resources: an `OpenFile` is the authority to use one descriptor
(its *position* in the view, because that is where POSIX puts it), and a
`PosixWorld` is the outside. **Any foreign operation that touches global state
receives the world explicitly**, which is what replaces a `modifies` clause over
the universe — and it means a caller can tell from a signature alone whether a
function can reach outside at all.

Authority for a descriptor is carved out of the world that has descriptors:
`open_file(&mut w, fd)`, with "is it really open" as a *precondition*. Same
division as `split_off` — the checker tracks tokens, the VCs track geometry, and
the state of the outside is geometry. `posix_world(script)` is the one place
authority appears from nothing, so the checker confines it to `test_` functions;
the script is what makes external behaviour something a test *author* controls
(one script shortens the second read, another fails the first), and the corpus
checks that a failed read leaves the buffer and the position exactly where they
were.

Handles are passed explicitly rather than owned by an RAII class, as this note
sequenced. `close` consumes the `OpenFile`, so a double close and a read after
close are both checker errors at the second use.

Three findings:

- **The exposure obligation caught the extern contract being
  under-specified**: a `read` post saying "these bytes came from the stream" says
  nothing about whether they are *bytes*, so the caller's `[u8]` could not be
  reconstructed. A world's stream is now a byte stream by well-formedness, stated
  for *every* index — off-the-end junk is our modelling choice as much as the
  stream is, and choosing it to be a byte removes a window premise from every
  read contract.
- **U4's "state effects functionally" lesson extends to foreign contracts.** The
  destination is one equation over `SpanView.fillFrom`, and since `n = 0` leaves
  every byte where it was, a short read and a failed read need no case analysis.
  Written as three clauses it needed two nested splits and did not close.
- **A wrapper that hides the world must say what it preserved.** `read_twice`
  could not prove its second read's precondition until `read_into`'s post said
  the handle survived — found by writing the second caller.

**The honest cost: this is the first rung whose safe wrapper needs a hand proof.**
`read_into` carries a three-line `discharge` on the exposure exit — not on its own
contract, which verifies automatically. `copy_prefix` needed nothing; a foreign
contract whose effect depends on an unpredictable outcome puts a case analysis in
front of the reconstruction. The tempting fix, a prelude lemma shaped to this one
signature, would be a prelude that knows about `posix_read`, which is worse than a
visible discharge in the subject that needs it.

Also structural rather than a gap: **resource-view contracts are not
monitorable**, because a view is ghost and at runtime there is nothing to look at.
The verifier covers those; the monitor covers how many bytes arrived and which
ones, and the test file carries `expect-skip` fences saying so.

Deferred with reasons: `open` (it needs a descriptor *and* authority — a product
type; the two-step carve is what avoids one) and `write` (symmetric to `read`, no
new question), plus interruption, partial writes, and any real libc binding.

### U7a — destruction semantics and resource fields *(done 2026-08-11, ADR 0029)*

`deinit` bodies run. The semantics were pinned before the restriction was lifted,
which is the order this note insisted on: the class invariant holds on **entry**
and is *not* re-established (there is nothing left to hold it, so a destructor
owes no `inv_exit` and has no `_old_self` twin); the body may move fields out,
which is how a class that owns authority hands it on; a moved field is not dropped
again, and the rest drop in reverse declaration order. The interpreter's order
within a drop is **invariant → body → remaining fields**, since checking after the
body would evaluate the invariant over a hole the body just made.

Classes hold resource fields, and `#[must_consume]` marks one whose authority must
go somewhere — abandoning it is a diagnostic, as is putting the marker on a class
with no destructor. An *unmarked* affine resource field may be abandoned: that is
a leak, and affine-not-linear authority permits leaks. The marker is what turns a
permitted leak into a diagnosed one.

**The most useful output of this rung is what it invalidated.**

- **U2a's mutable field borrow is sound in a destructor.** `&mut a.f` was deferred
  because a callee could not re-establish `a`'s invariant. In a `deinit` there is
  no invariant left to break, so the reason evaporates exactly where the invariant
  does — and `&mut self.w` is how the destructor hands its world to
  `posix_close`. Legal there and nowhere else.
- **U5's brand argument stopped being true.** It reasoned that only a raw or
  resource *return type* could launder a loan brand, because Sable had no
  storage-typed fields. Resource fields make a class exactly such a container.
  `class_holds_storage` decides it now, transitively. The lesson is not that the
  earlier argument was careless — it was correct when made — but that an argument
  from "the language has no X" expires when X arrives, and the ADR that made it
  should be re-read when it does.
- **`havoc_mut_borrow_args` assumed a borrow names a whole place**: `&mut self.w`
  replaced `self` with a view and lost the self-chain. A field borrow now writes
  the fresh state back into the base, leaving every sibling where it was.

Also: a by-value class argument now removes the value from its source place in the
interpreter — harmless while destructors were empty (the invariant check was
merely repeated) and a real double drop once bodies run.

`Ctx::is_partially_moved` was *deleted* rather than kept behind an `allow`: only
`self` can be partially moved today and `self` is not usable as a whole, so the
query has no reachable caller. Three lines to restore when one appears.

Deliberately not done: a leak *warning* for abandoned unmarked fields (the
diagnostic exists only for the marker, which keeps the signal high), and
`#[must_consume]` on locals and parameters — which is where it would catch a
forgotten `close` at a call site, and which needs the marker on a *type* rather
than a field.

### U7c — one ownership transfer *(done 2026-08-11, ADR 0030)*

Unscheduled, and added because an external review of U7a was right: ordinary
calls removed a by-value class argument from its source place and every other
transfer cloned. The finding generalised — the divergence was not a missing case
in one pass but a missing *notion* in both, so a move was written six times and
agreed nowhere.

One `take_place`/`drop_place` in the interpreter behind one `eval_moved`, and one
`transfer` in the checker at the matching sinks. Overwriting a place now runs a
full drop rather than repeating an invariant check; a returned local leaves with
the caller instead of being destroyed behind it; an owned parameter dies with the
callee's frame after its contract has been checked.

**What the sweep turned up is the argument for doing it before U7b**, which adds
sinks (`init`, `take`, `drop_in_place`, an arena owning `PointsTo` beside a
`SystemDealloc`) on top of this layer:

- `self.f = x` marked nothing, so a class could hold a resource the caller still
  named — duplicated authority through the one sink with no rule;
- an owned array moved into a field kept its old name alive, and a **verified**
  post was false at runtime. The v1 note calling this "not tracked" was
  documenting an unsoundness;
- `return self.f` handed a field's authority to a caller still holding the
  object. A member may now move a field out only if it puts something back:
  the invariant is stated over every field, and an invariant over a hole is not
  a question with an answer. Only a `deinit` may leave one — ADR 0029's rule,
  and precisely its reason;
- the loop-shape rule was resource-only, though its argument never mentioned
  authority;
- `#[must_consume]` meant "moved somewhere", which a temporary satisfied. The
  obligation now travels with the token, which is what `SystemDealloc` needs;
- adoption did not spend the world's claim on a descriptor, so affinity stopped
  reuse of one token but not minting a second. `PosixWorldView.claimed` and an
  `available` precondition fix it, with the monitor checking independently;
- three ICEs reachable from ordinary source, all missing match arms: a method
  assigning a resource parameter to a resource field, a call to a method
  returning a class or resource, and a function returning `raw<u8>`.

**Exact-once needs two corpus halves, and this is the reusable part.** "No value
is destroyed twice" is what the paths needed, and a compiler that destroyed
*nothing* would pass it: `corpus/tests/test_ownership.sable` uses a destructor
that falsifies its own invariant, so a second drop traps, and
`corpus/test-fails/deinit_runs.sable` gives a destructor a failing call to show
each path destroys at all. The second cannot live in `corpus/verifies` — a
verifying file may not contain a deliberately failing call.

**A third pass** closed four more: branch and loop joins carried only part of
the per-place state, so traversal order decided the rest (and because the move set
is a *union* over reaching branches, "consumed on one path" read as consumed — a
destructor that closed a handle only inside an `if` was accepted); the extern
return rule was a blacklist that named the storage types and missed the container;
an exposure body was left non-scoping by the second pass, so a derived local could
keep a name for storage the loan had given back; and generic class templates were
checked without the marker list, without the field-hole rule, and with **no
destructor checking at all**. `unsafe { }` is a marker and an exposure body is a
scope — the block grants vocabulary and has no lifetime, the exposure *is* one.

**A second review pass found four more of the same shape**, each the rule missing
from one more spot, and all four are now closed: `unsafe { }` and an exposure
body were scopes in the *interpreter* while the checker keeps their locals in the
function (an accepted program **panicked** the monitor); an inferred `var q =
raw_offset(p, 0)` dropped the loan brand a typed declaration computes; a
discarded class-valued call result was a temporary nobody destroyed; and a live
`#[must_consume]` place could be assigned over, which abandons the authority the
marker exists to protect. The standing limitation is now stated rather than
implied: passing a marked token by value discharges the obligation, so the marker
means *must leave this frame*, not *must reach a consuming primitive* — a
do-nothing sink satisfies it, and fixing that needs the marker on a type, which
is what `SystemDealloc` will force before U8.

### U7d — place-state closure *(done 2026-08-12, ADR 0030)*

The last representation boundary is explicit now: `Place::state_key` maps
`root + fields` to the complete `VarInfo` key, so `self.span` is never tested as
though its state lived under `self`. Loop and branch shape checks use it, and
exposure cleanup preserves move markers for outer fields. Cleanup also rejects
a must-consume token held by a disappearing local before deleting the scope.
Finally, a loop backedge must preserve brands and obligations as well as affine
liveness, so restoring the zero-iteration snapshot cannot erase a token that
migrated while every place remained live.

This changes the staging ahead. U7b's first allocator uses only a
program-lifetime static root and introduces no `SystemDealloc`. Before U8 adds
deallocation authority, mandatory consumption must move from a field annotation
to the resource type (or an equivalent declaration), propagate through owned
parameters, and be discharged only by a declared consuming operation. A
do-nothing by-value sink must not satisfy `SystemDealloc`.

### U7b — typed cells, layout, and static bump arena

**Slice U7b1 is complete (2026-08-12, ADR 0031):** `PointsTo<u64>` and
`CellState<u64>` now make one complete raw-span → typed-cell → raw-span
round trip. The checker transfers affine authority at both conversions; VCs
track provenance, alignment, and state; the interpreter and SVM keep an
abstract typed tag that excludes byte access; and the relational SVM still
agrees with its executable evaluator. Returning an empty cell to raw storage
zero-fills eight bytes as cleanup, without choosing a representation for an
initialized `u64`. Positive, negative, dynamic, direct-SVM, and differential
subjects cover the slice.

**Slice U7b2 is complete (2026-08-12, ADR 0032):** layout is now
compiler-established proof vocabulary. `Layout` records positive size and
nonzero power-of-two alignment; every fixed-width integer has a canonical
kernel-checked instance; generic clauses use `T.layout`, and concrete clauses
use `u64.layout`. `PointsToView` carries the layout, and the VC generator,
interpreter, and SVM take the `u64` cell geometry from their canonical type
mapping rather than duplicating the literal eight. This adds no byte
representation and no forgeable runtime layout value.

**Slice U7b3 is complete (2026-08-12, ADR 0033):**
`unsafe static_alloc(N) as (p, resource mem);` is the first root source. `N`
is a positive profile-bounded literal; the result is fresh provenance plus one
full uninitialized `RawSpan`, and there is deliberately no deallocation token.
The allocation remains live for the program execution, so the bindings are not
loan-branded and the resource may move into the bump arena. VCgen uses
`SpanView.uninit`; the interpreter keeps the allocation live; SVM lowering is
its existing fresh raw allocation instruction. Repeated execution creates
another leaking program-lifetime root rather than reacquiring a singleton.

**Slice U7b4 is complete (2026-08-12, ADR 0034):** `BumpArena` owns the
unallocated suffix of a program-lifetime root and carves one aligned
`u64.layout` extent per call. The implementation is ordinary safe source code
over `split_off`; its contract frames capacity and provenance so allocations
compose and a caller can relate the returned span to the root pointer plus the
pre-allocation cursor. Two blocks remain live and become typed cells in the
verified subject; a third allocation from a 16-byte arena fails at the public
space precondition.

Do not introduce `SystemDealloc` on this rung. The static root is deliberately
non-deallocating; that keeps typed-storage state and layout separate from the
interprocedural mandatory-consumption rule that U8 will need.

The explicitly laid-out record probe is green in Lean. Source-level POD values
remain deferred until they have direct runtime semantics; do not model them as
ordinary classes merely to satisfy the example, and do not introduce byte
serialization while doing so.

Exit criteria:

- alignment obligations are explicit and local;
- initialization state changes are reflected in views;
- typed values can be taken back to uninitialized storage;
- the arena's public allocation operation is safe;
- only root acquisition, typed storage operations, and raw accesses require
  unsafe blocks;
- the arena implementation does not contain one monolithic unsafe region.

### U8 — in-band free-list allocator

**The U8a entry gate is complete (2026-08-12, ADR 0035).** Mandatory
consumption is now a compiler-defined resource-type property. `OpenFile` is the
first instance: verified owned parameters inherit the obligation, returns move
it to a mandatory receiving place at the caller, class fields require a
destructor without an annotation, and every frame exit checks it. Only an
audited extern may mark an owned mandatory parameter `#[consumes]`; a verified
do-nothing sink, an unmarked extern, and an attribute on an affine resource all
fail locally. The strengthened POSIX contract is honestly versioned as
`posix.close.v2`.

Next add `SystemDealloc` under that rule, then allocator identities,
`BlockLease`, in-band headers, free, and coalescing. A compiler-sealed release
operation is the terminal consumer; no user function may declare itself one.

**The U8b system-root slice is complete (2026-08-12, ADR 0036).**
`system_alloc` returns a fresh base, the complete raw extent, and mandatory
`SystemDealloc`; `system_dealloc` consumes the latter two only after a local VC
ties base pointer, allocation identity, zero offset, and original length
together. It is the compiler-sealed terminal operation and lowers to SVM
`rawFree`. A foreign declaration cannot promise the release away. Typed
storage must return to raw and carved extents must rejoin before release.

Next introduce allocator identities and `BlockLease`, then store the free-list
metadata in the root's free blocks. The allocator retains `SystemDealloc` until
its own destruction; client `free` consumes leases, not the system token.

**The U8c authority shape is proved (2026-08-12, ADR 0037).** `BlockLease`
is the refined byte authority itself, with allocator identity, block key, and
`SpanView` in one view. Typed role changes preserve the allocator/key pair
rather than degrading a lease to plain `PointsTo<u64>`. One affine allocator
aggregate owns the dynamic free map; sealed `take` partitions one entry into a
lease and sealed `put` reverses that transition. The standalone Lean probe
proves partition, disjointness, round-trip restoration, and typed-role
preservation.

Next implement that narrow resource surface in the compiler. Do not expose a
standalone lease-to-span escape hatch: mandatory leases terminate only by
returning to their matching aggregate. Once the vertical slice is pinned by
wrong-allocator, double-put, abandoned-lease, and typed-round-trip subjects,
add allocator-owned free-block roles and the in-band header algorithm.

**The U8c compiler slice is complete (2026-08-12, ADR 0038).** A complete
`RawSpan` folds into mandatory `AllocatorState`; sealed take/put is the only
source/sink of mandatory `BlockLease`; and destruction returns the current
complete raw root for the existing `SystemDealloc` path. The typed `u64` role
is `LeasedPointsTo<u64>`, so allocator/key identity and the must-consume
obligation survive init/read/take/drop and conversion back. Completeness tracks
root geometry rather than freezing client byte contents. The positive vertical
subject proves 10/10 and executes dynamically; seven negative subjects pin the
boundary, and the complete single-job suite passes.

Next add an allocator-owned `FreeBlock` role plus sealed split/reinsert
transitions. That is the missing authority vocabulary for writing and walking
in-band headers without turning an internal free extent into a client lease or
exposing a general lease-to-span escape hatch.

**The U8d free-block authority shape is proved (2026-08-12, ADR 0039).**
`FreeBlock` is a mandatory allocator-internal role with offset-derived keys.
Only it may split/join; the client receives a nonsplittable `BlockLease` through
an explicit consuming role change. The Lean probe proves well-formed prefix and
suffix keys, coverage, disjointness, adjacency, byte-preserving rejoin, and
aggregate take/put restoration.

Next implement the sealed `FreeBlock` operations vertically, then add an
identity-preserving typed header role for the in-band links.

**The U8d compiler slice is complete (2026-08-12, ADR 0040).** Sealed
aggregate take/put now traffic in mandatory `FreeBlock`; only that internal
role may split and join, while explicit consuming role changes preserve the
allocator/key/extent identity of a nonsplittable client `BlockLease`.
`allocator_create` proves the zero-offset positive-root condition needed by
the initial offset-derived key. The positive subject splits a 16-byte root,
runs the 8-byte prefix through `LeasedPointsTo<u64>`, returns it, coalesces both
blocks, and releases the system allocation: 15/15 obligations and a passing
dynamic value check. Eight negative subjects pin abandonment, degenerate
splits, bad adjacency/order, wrong ownership, client splitting, and extern
smuggling.

Next prove the smallest identity-preserving header role needed for in-band
links. Keep list policy and traversal out of that proof: first establish that
typing, updating, and clearing a header cannot change allocator identity,
block key, or the remaining payload extent. Then implement one linked free-map
walk vertically before adding allocation policy or randomized testing.

**The U8e header authority shape is proved (2026-08-12, ADR 0041).** A real
in-band node needs two aligned `u64` cells: whole-block size and next key. The
first one-word probe was rejected because ghost `SpanView.len` erases and
cannot drive runtime splitting. The corrected `FreeHeaderView` retains
allocator identity and block key beside distinct size/link cells and the raw
payload; its 16-byte minimum, disjointness, field updates, `u64` bounds,
clearing, and whole-block round trip are kernel-checked.

Next implement only this mandatory header role and its sealed transitions.
Then probe one traversal step and choose a sentinel/link-order policy from the
proof and runtime needs; do not bury that decision inside the eventual search
loop.

**The U8e compiler/runtime slice is complete (2026-08-12, ADR 0042).**
`FreeHeader` is one mandatory static role over two real typed cells and the
remaining raw payload. Unsafe conversion checks the aligned 16-byte minimum;
initialization stores exact whole-block size plus next key; reads and clearing
track each cell state; conversion back zero-fills the header words and restores
one well-formed `FreeBlock`. Composite operations lower to pairs of the SVM's
existing typed-cell instructions, so no parallel header-memory semantics was
introduced. The positive path proves 13/13 and executes, seven negative
subjects pin the boundary, two SVM subjects agree, and the full serial corpus
passes.

Next choose and prove the traversal policy. The likely candidate is a sorted
offset-key list with `root.len` as its one-past-end sentinel: every live block
key is strictly below it, it fits the stored `u64`, and adjacency/coalescing
become local arithmetic. The proof must also make the runtime head explicit;
`AllocatorState` erases, so the algorithm needs an ordinary `u64` head paired
with that authority rather than pretending the ghost free map can be read.

**The U8f traversal policy is proved (2026-08-12, ADR 0043).** The free list
is a finite chain sorted by root-relative block offset, with `root.len` as its
end sentinel and an ordinary safe `u64` head paired with erased allocator
authority. Each real node has at least the 16-byte header, ends no later than
its successor, and links no farther than the sentinel. Those local facts prove
header containment, bounded runtime fields, acyclicity, and strict decrease of
the loop variant `root.len - current`. Equality identifies adjacent blocks;
aligned splits retain a suffix only when it can hold another header.

Next implement one checked traversal step vertically before attempting the
full first-fit loop. Keep predecessor-link mutation and allocation policy out
of that slice so the relationship between the ordinary head/current offsets
and the erased aggregate authority is explicit and independently tested.

**The U8f1 stored-header transfer slice is complete (2026-08-12, ADR 0044).**
`AllocatorState` can now park initialized `FreeHeader` authority in a map
disjoint from raw free spans and temporarily extract it at an ordinary runtime
`u64` key. The real typed cells remain in place while only affine authority
moves. Aggregate completion requires every stored header to be cleared and
returned; map-disjointness prevents a header and byte/block role from claiming
the same key. The positive subject proves 20/20, executes to 64, and restores
the system root; missing-entry and wrong-owner subjects fail at the intended
sealed operations. The full single-worker corpus and all focused regressions
pass.

Next lift ADR 0043's finite sorted-chain predicate into `AllocatorView`.
Extraction must then supply the local `16 ≤ size`, `key + size ≤ next`, and
`next ≤ root.len` facts, while reinsertion preserves the chain. Do not write
the first-fit loop while those facts still come only from a concrete test's
literal header values.

**The U8f2 stored-chain shape is proved (2026-08-12, ADR 0045).** A structural
`StoredChain state limit current` ties each reachable runtime key to the exact
initialized header held by the aggregate and carries the sorted/disjoint local
facts plus the tail witness. A non-sentinel step now derives header
extractability, field witnesses, local bounds, and strict decrease of
`limit - current`; reinserting the extracted header restores the entire
allocator view by equality. The probe also constructs the initial one-node
chain whose link is the root-length sentinel.

Next integrate this predicate into the compiler surface. Keep the existing
two-argument header take as the low-level authority transfer, but add a
policy-bearing checked traversal operation that receives both ordinary
`limit` and `current`, rejects the sentinel, and requires the matching
`StoredChain`. Use that operation in the positive subject before attempting a
loop or predecessor-link mutation.

**The U8f2 compiler slice is complete (2026-08-12, ADR 0046).**
`allocator_step_header(&mut state, limit, current)` now requires a
non-sentinel `StoredChain state limit current` and transfers the exact stored
header without adding a runtime instruction. The positive subject constructs
the initial chain and proves its runtime header-size, ordering, and root-bound
assertions from `StoredChain.step` plus the values actually read from memory;
it remains 20/20 and dynamically returns 64. Sentinel traversal fails at the
new named obligation. The complete single-worker corpus and focused
regressions pass.

Next write a read-only traversal loop that reinserts every inspected header
before advancing. Its invariant must pair the ordinary `current` value with
the tail `StoredChain`, and its variant must be `limit - current`. Stop before
predecessor-link mutation, splitting, or leasing: first test whether loop havoc
preserves this proof shape cleanly with zero `assume` and zero `defer`.

Exit criteria:

- allocation transfers exactly one disjoint region;
- free consumes the matching lease;
- wrong allocator, double free, and freeing a subregion fail locally;
- coalescing is proved through span adjacency/join;
- allocator invariant accounts for the entire root allocation;
- randomized dynamic tests compare against a simple reference allocator;
- zero `assume` and zero `defer` inside the allocator.

### U9 — aggregate resources and intrusive list

Implement the real `ResourceMap` operations and an intrusive doubly linked list
whose nodes live in one arena for the first version.

Runtime state:

```text
head : option<raw<Node>>
tail : option<raw<Node>>
```

Erased state:

```text
resource ResourceMap<NodeId, PointsTo<Node>> nodes
```

Exit criteria:

- list invariants relate raw links to an abstract sequence;
- each node permission is borrowed or extracted through sealed aggregate
  operations;
- no explicit separating conjunction appears in the Sable source;
- pointer comparisons needed by the list have a clear live-provenance rule;
- proof scripts remain about the abstract list and map, not global heap
  rearrangement.

If this fails, revise the resource API before attempting MMIO or kernel work.

### U10 — MMIO and privileged-state profile

Only after the raw-memory and resource architecture has survived U9:

- add trace events and input oracles to a profile-specific machine model;
- add platform-provided MMIO capabilities;
- verify a UART polling/transmit driver;
- expose trace projections in contracts;
- later add page-table and privileged instruction subjects against a formal ISA
  profile.

Concurrency, DMA ownership transfer, and atomics remain out of scope.

## Corpus plan

### `corpus/verifies`

```text
resource_flow.sable
unsafe_copy.sable
ffi_fill.sable
posix_file.sable
bump_arena.sable
free_list.sable
intrusive_list.sable
uart.sable
```

### `corpus/must-fail`

```text
resource_use_after_move.sable
resource_double_borrow.sable
resource_branch_shape.sable
resource_loop_shape.sable
raw_escape.sable
raw_outside_unsafe.sable
raw_bad_join.sable
raw_uninitialized_read.sable
raw_wrong_allocator.sable
raw_double_free.sable
```

Some names above are verification failures rather than checker failures; each
file should assert the stable diagnostic or obligation name appropriate to its
layer.

### `corpus/test-fails`

Dynamic tests for bypassed/malformed operations:

```text
raw_oob.sable
raw_use_after_free.sable
raw_type_confusion.sable
raw_overlap_copy.sable
```

### `corpus/svm-diff`

Add direct SVM subjects for every raw operation, both successful and `undef`,
plus evaluation-order cases where the identity of the first failing operation
matters.

## Prototype acceptance criteria

The architecture passes its first experiment only if all of the following hold.

1. `copy_prefix` has a short value-level contract and contains no explicit heap
   predicate.
2. Duplicate authority, use after move, borrow conflict, and exposure escape are
   named checker diagnostics with precise spans.
3. Bounds, initialization, pointer/span correspondence, and adjacency are named
   Lean obligations with useful contexts.
4. Splitting produces independently usable resources that can be rejoined.
5. Resource views version correctly after mutation; stale facts cannot survive
   a call, branch join, or loop head.
6. The Lean probe proves preservation of the hidden resource-context
   interpretation.
7. The relational SVM, Lean evaluator, and Rust interpreter agree on raw-memory
   examples.
8. No `assume` or `defer` is needed for the byte-only vertical slice.
9. The compiler reports unsafe blocks separately from actual trust dependencies.
10. Folding evidence leaves a safe wrapper that reads like ordinary Sable.

Failure of any item is useful information. The response should be to simplify or
strengthen the resource abstraction, not to expose general separation logic
prematurely.

## Explicitly excluded from unsafe v1

- general integer-to-pointer conversion;
- escaping raw pointers to movable safe locals;
- retained foreign pointers and callbacks;
- general `transmute`;
- unions and packed records;
- arbitrary byte access to typed objects;
- bytewise copying of pointer-containing values without a proved
  `BitwiseCopyable` instance;
- arbitrary classes or destructor-bearing values in raw typed storage;
- atomics, DMA, concurrent shared raw memory, and rely-guarantee reasoning;
- `defer` for ownership, provenance, initialization, or liveness;
- a user-visible general separation logic;
- a full VCgen soundness proof as a prerequisite for the prototype.

## Decisions deliberately left to the probes

1. **Exact resource syntax.** The category must be program syntax; the precise
   placement of `resource` is cosmetic until U2b.
2. **Typed-extent representation.** U1 should determine whether a side table,
   extent partition, or another concrete Lean encoding gives the cleanest
   preservation proofs.
3. **Pointer equality.** Ordering/subtraction are same-provenance. The live
   cross-allocation equality rule must be validated against the intrusive-list
   and native-refinement stories.
4. **User-defined resource types.** Built-ins suffice through U5. The POSIX and
   aggregate-resource phases will reveal the minimum declaration mechanism.
5. **Mandatory cleanup.** Affine authority gives safety; linear or
   `#[must_consume]` resources give leak freedom. Do not conflate them.
6. **Manifest granularity.** Module-level first; per-export once the format and
   call-graph behavior are stable.
7. **Trace visibility.** Start with full traces in the formal model and expose
   projection functions in contracts; do not commit every driver API to raw
   event lists.

## Bottom line

The central bet remains:

> **Make raw pointers useless without affine erased resources, and make those
> resources visible to Lean only through pure views.**

The current repository has already validated the first half of the checker
story: affine moves are source-level flow facts, and the logic reasons about the
same class value whether it arrived by borrow or by move. The next argument
should be executable. Start with the concrete Lean probe, then a byte-only
resource checker and raw SVM heap, and stop at `copy_prefix` long enough to judge
whether the abstraction really preserves Sable's readability.
