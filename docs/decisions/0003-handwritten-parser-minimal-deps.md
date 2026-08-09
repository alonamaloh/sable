# ADR 0003 — Handwritten recursive-descent parser; minimal dependencies

**Decided 2026-08-08.**

Parser: handwritten recursive descent with error recovery, not a parser generator. Reasons: diagnostic quality is a stated project priority (LLMs are the primary writers of Sable code and live off error text), and the M4 LSP needs resilient parsing of incomplete programs — both are things generators are bad at. The `///` block-attachment rules (positional, blank-line-sensitive, normative) also want a custom scanning layer.

Dependencies: keep the Rust side near-zero-dep (`serde`/`serde_json` for Lean's JSON diagnostics; that's about it for M0). Every dependency is a supply-chain and build-time cost on a project whose pitch is a small trusted base; add them when they earn their place, not before.
