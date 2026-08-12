# ADR 0050 — Allocation returns an exact reinsertion frame

**Decided 2026-08-12.** First-fit allocation already returned the exact byte
extent removed from the stored chain, but its public contract exposed only the
lease key, length, owner, and root provenance. Client `free` needs a stronger
fact: materializing an in-band header at that key must not collide with
allocator authority.

## Decision

`AllocatorView.returnable state lease` is the narrow frame passed from
allocation to insertion. It states that:

- the lease belongs to the allocator and both aggregate maps are empty at its
  exact key;
- its key is its span offset, its length is positive, and its allocation
  provenance is the allocator root's provenance; and
- no free or header entry begins strictly inside the lease extent.

Removing an exact stored head now proves this predicate after clearing its two
typed header cells. Prefix allocation preserves it for the returned prefix,
and parking the suffix header at the prefix boundary preserves it again. Thus
both whole and split head allocation return a lease that the resulting
allocator can accept without reconstructing byte-layout facts at the caller.

The first insertion vertical is deliberately ordinary verified Sable policy.
`free_list_insert_head` consumes the mandatory `BlockLease`, changes it to an
allocator-internal `FreeBlock`, writes its real size and old-head link into the
in-band header, parks that header in `AllocatorState`, and advances the safe
runtime head. Its precondition records the exact key and size plus the sorted
boundary `key + size <= old head`; its postcondition restores `StoredChain`.
No new sealed allocator operation is needed.

Two general kernel lemmas make the intended composition explicit:
`returnable_prefix` retains the frame for a positive prefix, while
`returnable_putHeaderOutside` retains it when a header is stored wholly before
or after the client extent.

## Evidence and boundary

The removal, allocation, and insertion subjects prove every obligation with
zero assumptions and zero deferrals. Dynamic split and whole fixtures now
allocate a lease and return that same mandatory resource through
`free_list_insert_head` before clearing the list and releasing the exact
system root.

This decision proves front insertion, not arbitrary sorted insertion or
coalescing. `returnable` rules out entries at or inside the returned extent;
it intentionally does not pretend that this alone identifies a predecessor
or proves a predecessor ending before the lease. The next slice must carry an
explicit insertion-location/gap witness through a read-only search, then use
that witness to rebuild a predecessor link. Coalescing follows only after that
structural insertion proof is stable.
