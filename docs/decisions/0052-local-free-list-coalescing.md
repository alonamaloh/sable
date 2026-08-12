# ADR 0052 — Public lease return coalesces local neighbors

**Decided 2026-08-12.** ADR 0051 proved arbitrary sorted reinsertion, but
deliberately left adjacent blocks separate. That was the right intermediate
boundary: it isolated address search and predecessor relinking before adding
the authority changes needed to clear and join neighboring in-band headers.

## Decision

`free_list_return` is the public lease-return policy. It consumes the exact
mandatory `BlockLease`, locates its proved sorted gap from real links, reads
the real predecessor size when one exists, and dispatches over four explicit
adjacency cases:

| predecessor adjacent | successor adjacent | transition |
|---|---|---|
| no | no | ordinary sorted insertion |
| yes | no | join predecessor and returned block |
| no | yes | join returned block and successor |
| yes | yes | join predecessor, returned block, and successor |

The noncoalescing `free_list_insert` remains as a useful verified primitive;
changing its semantics would make the already-proved insertion transition
less precise. The public operation composes it with four focused coalescing
functions instead.

Every merge is an authority transition, not arithmetic metadata editing.
Adjacent stored headers are extracted, their two typed cells are cleared back
to `FreeBlock`, and `free_block_join` proves allocator identity, provenance,
order, and exact span adjacency before producing the combined block. Only then
is one final header materialized. A predecessor link is rebuilt only when the
merged block does not itself begin at that predecessor.

The root-length sentinel is never treated as a header. Successor coalescing is
therefore gated by `current != limit`. Predecessor-only coalescing explicitly
allows `current = limit`; this covers a returned extent ending exactly at the
root boundary without inventing a successor node.

The supporting `InsertionLocation` theorems preserve the entire untouched
prefix and suffix while proving the rebuilt `StoredChain`. The public postcondition
exposes only that restored chain and the unchanged limit, so callers neither
select a coalescing branch nor supply a trusted predecessor size.

## Evidence and boundary

`free_list_return.sable` verifies all 94 obligations across its ten-function
module closure with 16 visible unsafe regions and zero `assume` or `defer`.
The unsafe regions contain only the already-delimited in-band header reads,
clears, and initializations; search, adjacency policy, branch selection, and
list-state updates are ordinary verified Sable.

Six dynamic fixtures cover head-successor, predecessor-only, successor-only,
both-neighbor, predecessor-at-sentinel, and separated insertion. Every fixture
clears the resulting headers, reconstructs the exact original root authority,
destroys the allocator, and performs the sealed system release.

Three local negative guards pin the public boundary: a lease from another
allocator fails the `returnable` call precondition, a second return fails as a
resource use after move, and substituted subregion metadata fails the public
key and size preconditions.

A deterministic host-side differential harness compensates for resource
arrays not yet existing in Sable. It generates statically named leases for 12
fixed-seed permutations of 12 blocks (144 returns), runs the real Sable
interpreter, and after every return compares the runtime head and every stored
`(key, size, next)` header against a small independent coalescing model. The
seeds cover all four adjacency cases and are fixed so a failure is replayable.
The complete corpus passes with `SABLE_TEST_JOBS=1` and one Rust test thread
(256.46 seconds), including the warning-clean positive set, exact-diagnostic
negative set, monitored dynamic fixtures, and dynamic failure subjects.

This closes U8's allocator experiment. Whole-root accounting still rests on
the intended two-layer invariant: the affine resource context partitions
authority between `AllocatorState` and live mandatory leases, while
`allocator_destroy` is provable only after all roles rejoin into one key-zero
span with the root's exact allocation, offset, and length and no stored
headers. The pure `StoredChain` describes list policy; it is not presented as
a second, duplicative ownership logic.

The next experiment is U9: generalize the specialized aggregate operations
into a reusable `ResourceMap` and use them to verify an arena-backed intrusive
list. No general separating conjunction is introduced by this decision.
