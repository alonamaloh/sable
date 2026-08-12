# ADR 0045 — Traversal is governed by a stored-chain witness

**Decided 2026-08-12.** ADR 0044 made initialized header authority storable,
but did not yet connect the aggregate's header map to ADR 0043's sorted-list
policy.

## Decision

The proof-level traversal invariant is a structural `StoredChain` indexed by
the allocator view, root-length sentinel, and ordinary runtime head:

```text
StoredChain state limit current
```

Its terminal constructor requires `current = limit`. Each real constructor
names the exact header stored at `current`, its initialized size and next
values, allocator ownership and well-formedness, and the local constraints:

```text
0 <= current
16 <= size
current + size <= next
next <= limit
StoredChain state limit next
```

This is deliberately structural rather than merely a universal predicate over
the header map: it proves finiteness, rules out cycles, and provides the tail
witness needed at the next loop iteration.

A nonterminal chain step proves that the current header is extractable, exposes
its initialized field values and local geometry, and strictly decreases
`limit - current`. Extracting and reinserting that exact header restores the
allocator view by equality, so the original chain and its tail remain valid.
A construction lemma proves the one-node initial list after storing a header
whose next link is the sentinel.

## Evidence and compiler consequence

`docs/notes/stored-free-list-chain-probe.lean` kernel-checks stored-entry lookup,
takeability, step elimination, variant decrease, exact extract/reinsert
restoration, and initial single-node construction.

The current two-argument `allocator_take_header(state, key)` is therefore only
the authority primitive from ADR 0044. The checked traversal operation should
also receive the ordinary `limit` and require `key != limit` plus
`StoredChain state limit key`. Its generated context can then relate later raw
header reads to the chain's size/next witnesses. This policy-bearing operation
should be introduced before any loop; the lower-level primitive must not be
mistaken for proof that arbitrary stored headers form a valid list.
