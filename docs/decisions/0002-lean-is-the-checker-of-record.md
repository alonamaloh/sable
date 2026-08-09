# ADR 0002 — Lean is the elaborator and checker of record, from day 1

**Decided 2026-08-08.**

The proof language is real Lean elaborated against the `Sable` prelude — not a fixed expression grammar translated to SMT by the Rust side. There is exactly one semantics for proof-language text, from the first commit; the "M4 seam" (bolting Lean onto an SMT-first verifier later) never exists.

Corollary: **no external SMT solver, ever.** Routine obligations go through an in-Lean automation portfolio (`omega`, `grind`, `bv_decide`, `simp` — see `lean/Sable/Auto.lean`); all proofs are kernel-checked. This makes stage-1 trust (design §10.1) strictly smaller than the design doc's original SMT architecture: the trusted base is the Rust VCgen/emitter plus the Lean kernel, with no solver in between. The design doc's §6/§10 "SMT backend" language should be revised to match once M1 confirms portfolio coverage.

Accepted risks, watched via the corpus: Lean cold-start latency (mitigations: pinned toolchain, prebuilt prelude oleans, later a persistent server), toolchain churn (pin + deliberate upgrades), automation coverage unknowns (`discharge` is the designed pressure valve).
