# ADR 0004 — Signed `/` and `%` are Euclidean, not C-truncating

**Decided 2026-08-08 (Alvaro).**

Sable's integer division rounds down rather than toward zero; specifically it is **Euclidean division**: `a = b * (a / b) + a % b` with `0 ≤ a % b < |b|`. The remainder is always non-negative.

Why Euclidean rather than C truncation ("C's messed-up semantics" — the words of the language designer) or floor:

- The remainder invariant `0 ≤ a % b < |b|` is the algebraically cleanest of the three conventions (Boute, *The Euclidean definition of the functions div and mod*, TOPLAS 1992).
- It is exactly Lean core's `/` and `%` on `Int`, so the program operation and the proof-language operation are **the same function** — clauses mentioning `/` mean precisely what the program computes, with zero translation. (Floor and Euclidean agree whenever the divisor is positive; they differ only for negative divisors, where floor gives `7 / -2 = -4` and Euclidean gives `-3`.)
- `omega` understands Lean's `ediv`/`emod` natively.

Obligations stay as in design §2.2: `b ≠ 0` for `/` and `%`; additionally `¬(a = T.min ∧ b = -1)` for signed `/` (the one quotient that overflows; `T.min % -1 = 0` is fine). Unsigned division needs only `b ≠ 0`.
