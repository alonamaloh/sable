# ADR 0001 — Compiler implemented in Rust

**Decided 2026-08-08.**

The compiler will live for years and wants long-term tool quality: the ecosystem has what we need (process orchestration, JSON, eventually `lsp-server`), ownership-flavored IR design is natural, and single-binary distribution matters for a toolchain. Considered: Lean 4 end-to-end (thinner Lean seam, but slower everyday engineering and a much smaller ecosystem); C++ (viable, no advantage here).

Consequence: the Lean seam is a process boundary (`lake env lean --json`), so the emitter and the source map are load-bearing (see ARCHITECTURE.md).
