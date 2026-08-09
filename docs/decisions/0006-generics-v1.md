# ADR 0006 — Generics v1: explicit instantiation, monomorphize-then-check

**Decided 2026-08-09.** The Vec benchmark (goals doc, Tier 1) forces the
first cut of the generics design. Monomorphization-before-VC-generation
was committed long ago (design §12); this ADR fixes the v1 surface and
the compiler strategy.

1. **Surface**: type parameters on classes and functions —
   `class Vec<T> { [T] buf; ... }`, `fn swap_elems<T>(&mut [T] a, u64 i, u64 j)`.
   Instantiation is **always explicit**: `Vec<i32>::with_capacity(4)`,
   `swap_elems<u8>(&mut a, i, j)`. No inference in v1 — honest and
   unambiguous; inference is sugar that can come later without semantic
   change.
2. **Parameter domain v1**: the eight integer types. (`bool`, class-typed
   parameters, and nested instantiations come later; class fields still
   cannot be class-typed, so `Vec<Vec<T>>` is out of range anyway.)
3. **Strategy: parse → expand → everything else.** A monomorphization
   pass clones each generic declaration once per distinct instantiation
   reachable from non-generic roots, substituting the parameter
   everywhere it occurs — including **as a token in proof-clause text**
   (so `T.max` in a contract becomes `i32.max`). The checker, VCgen,
   Lean emission, interpreter, and LSP see only ordinary declarations;
   the Lean encoding needs nothing new.
4. **Naming**: instances are mangled `Vec_i32` (Lean structure names,
   theorem prefixes); diagnostics and obligation names display the
   pretty form `Vec<i32>::push`. Spans point into the generic source.
5. **Proof cost**: each instance is verified independently. Accepted for
   v1 (automation is cheap; instances differ in range facts anyway).
   Proving once and instantiating — a per-instance `∀`-quantified
   metatheorem — is future work tied to the metatheory track.
6. **Law-carrying trait bounds are deferred to the hash-map benchmark**
   (`T: Hashable` with hash-respects-equality), exactly as the goals doc
   schedules: Vec needs no bounds, so v1 ships without them rather than
   speculating.
