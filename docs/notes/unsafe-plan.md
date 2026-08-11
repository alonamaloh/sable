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

#### U2a — general place/borrow engine (safe side)

- a reusable `Place` AST: `local | self | Place.field`, with room for later
  projections;
- checker state per place: `live | moved | shared-borrowed(n) | mutably-borrowed
  | partially-moved`;
- branch and loop joins over that state (ADR 0021's rule generalized: a
  returning branch reaches nothing);
- the ordinary-class features that ADR 0020 deferred and that this engine makes
  cheap — local-to-local class moves, general `&mut C`;
- named diagnostics, replacing the ad hoc `moved` bit.

`&mut C` is the point of doing this first: it is a safe-side consumer with an
existing corpus to shake the engine out on (`Integer`'s arithmetic could mutate
in place instead of returning fresh values), and it isolates the ownership work
from the raw-memory model. Nothing forces `&mut C` on its own — building it
here is paying for a test surface, and that is the honest reason.

Exit criteria:

- local-to-local moves and `&mut C` verify on corpus subjects;
- borrow conflicts and use-after-move are named diagnostics with spans;
- existing class affinity tests remain green, with the `moved` bit gone.

#### U2b — resource category on the same engine

- parser/AST support for resource locals, parameters, returns, and borrows;
- `Ty::Raw` and resource-type identities;
- resource liveness and borrow state, reusing U2a's lattice unchanged;
- resource-shape checks at branch joins and loop backedges;
- erasure from runtime signatures;
- pure resource-view binders in Lean emission, versioned separately from token
  identity.

Keep scope narrow:

- built-in `RawSpan` only;
- no resource fields yet;
- no user-defined resource types;
- no raw machine operations yet;
- no partial move from ordinary class fields.

A checker-only corpus should establish moves, borrows, branches, loops, returns,
and compile-fail behavior before raw memory arrives.

Exit criteria:

- a resource can be passed by value and returned;
- shared and mutable resource borrows are checked;
- duplicate use and conflicting borrows are source diagnostics;
- fall-through branch mismatch is rejected;
- a loop must preserve resource shape while its views change;
- resource parameters do not appear in interpreter/native runtime arguments;
- no second ownership system exists anywhere in the compiler.

### U3 — byte raw heap in the formal SVM

Add the byte-only raw heap and operations to the normative SVM, evaluator, Rust
lowering, and differential harness.

Operations:

```text
fresh loan/root allocation
pointer add
load8
store8
take8
free
```

No lexical exposure yet; direct SVM subjects exercise the semantics.

Exit criteria:

- agreement in both directions re-proved;
- determinism, totality, and progress restored;
- valid and invalid raw subjects added to `corpus/svm-diff`;
- injected wrong lowering is detected;
- invalid load/store/free reaches the intended `undef` outcome.

### U4 — lexical byte exposure and `copy_prefix`

Add hidden loan brands, shared/mutable exposure, `RawSpan` split/join, and byte
intrinsics to the Sable compiler and interpreter.

Primary subject:

```text
corpus/verifies/unsafe_copy.sable
```

with `copy_prefix` as above.

Required negative subjects:

```text
return pointer from expose
store pointer in outer local
leave a split span unjoined
use resource after move
borrow source mutably while shared
read an uninitialized byte
range beyond span
invoke raw load outside unsafe
```

Exit criteria:

- `copy_prefix` verifies with no `assume`, `defer`, or user-visible heap logic;
- dynamic tests cover empty, partial, and full copies;
- mutable exposure reconstructs the final safe array;
- shared exposure cannot mutate;
- all pointers/resources carrying the loan brand are gone at scope exit;
- unsafe-block counts appear in build output.

This is the first go/no-go checkpoint. Do not proceed to allocators if the safe
wrapper is proof-noisy or if the checker cannot explain failures locally.

### U5 — deterministic extern shim and trust manifest

Add:

- `extern "C"` declarations with mandatory structured audit metadata;
- erased resource parameters;
- noescape pointer arguments;
- resource-shaped effects;
- a deterministic test shim (`fill`, `copy`, or `checksum`);
- module-level trust manifests stored beside content-addressed artifacts.

Exit criteria:

- a safe Sable wrapper around `c_fill` verifies;
- the foreign implementation receives only ABI values;
- mutation is reflected in the returned resource/safe array view;
- undeclared mutation is impossible at the Sable call boundary;
- importing the wrapper imports its trust manifest transitively;
- build status says “verified relative to audited boundary,” not “fully
  verified.”

### U6 — POSIX-shaped handles and scripted worlds

Add built-in or minimal user-definable non-memory resources sufficient for:

```text
OpenFile
PosixWorld
```

Implement safe wrappers for `read`, `write`, and `close` against test stubs
before binding a real libc.

**Handles are passed explicitly here, not owned by an RAII class**
(`fn close(i32 fd, resource OpenFile open)`). A `File` class whose destructor
closes the handle needs non-empty `deinit` and the destruction semantics above,
which is U7a work; forgetting to call `close` leaks a descriptor, which is
exactly what affine-not-linear authority permits and what `#[must_consume]`
later diagnoses.

Exit criteria:

- `close` consumes `OpenFile` exactly once;
- read mutates only the passed buffer and world/file state;
- short reads and errors are represented in the contract;
- `sable test` can script external input and failures;
- resource/extern assumptions appear in the manifest;
- no retained pointer is permitted.

### U7a — destruction semantics and resource fields

Lift the empty-`deinit` restriction with the semantics pinned above: invariant
assumed on entry and not re-established, fields movable out of the body, no
double drop, monitor ordering fixed in the interpreter, `partially-moved` in the
place engine. Add resource fields in classes and `#[must_consume]`.

Exit criteria:

- a class destructor consumes a resource field exactly once;
- a partially-moved class drops only its remaining fields, in reverse order;
- the dynamic invariant monitor runs before the body, never over a hole;
- an abandoned `#[must_consume]` field is diagnosed; an ordinary affine field is
  not.

### U7b — typed cells, layout, and static bump arena

Add:

- `Layout<T>`;
- abstract typed extents;
- `PointsTo<T>` with `CellState<T>`;
- init/read-copy/take/drop-in-place operations;
- root/static allocation sources;
- a program-lifetime static bump arena.

Use fixed-width integers first. Add one explicitly laid-out record only after the
integer path works.

Exit criteria:

- alignment obligations are explicit and local;
- initialization state changes are reflected in views;
- typed values can be taken back to uninitialized storage;
- the arena's public allocation operation is safe;
- only root acquisition, typed storage operations, and raw accesses require
  unsafe blocks;
- the arena implementation does not contain one monolithic unsafe region.

### U8 — in-band free-list allocator

Add allocator identities, `BlockLease`, in-band headers, free, and coalescing.

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
