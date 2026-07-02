# Knowledge Base: cantor-diagonalization-oq-01-oq-01-wip-01

## Problem Understanding

Parent `cantor-diagonalization-oq-01-oq-01` proves an intermediate cardinal
(ℵ₀ < κ < 2^ℵ₀) exists **iff CH fails**. This WIP answers the finer, purely
ZFC-provable **structural** question: *which* cardinals are the intermediates,
and is there a least one?

## Insights

- Every cardinal ≥ ℵ₀ is an aleph (`mem_range_aleph_iff`), so every intermediate
  is `ℵ_o`; being > ℵ₀ = ℵ_0 forces `o > 0`. No exotic intermediates.
- `aleph_lt_aleph` / `aleph_le_aleph` transport cardinal comparisons to ordinal
  index comparisons — the workhorse of the file.
- ℵ₁ is a uniform lower bound (nothing strictly between ℵ₀ and ℵ₁), and is
  itself intermediate iff ¬CH; hence ℵ₁ is the least intermediate when any exists.
- The continuum is always an aleph `𝔠 = ℵ_δ`; the intermediates are exactly
  `{ℵ_o : 0 < o < δ}` — an order-iso with the ordinal interval (0, δ).
  CH is δ = 1 (empty); ¬CH is δ ≥ 2.

## Result

Shipped `CantorDiagonalizationOQ01OQ01Wip01.lean`, 185 lines, 12 theorems,
2 definitions, **0 axioms** (#print axioms: propext, Classical.choice, Quot.sound).
Verified via `lake env lean`. PR #33075.

## Dead Ends

- None; single clean pass. Universe metavariables required pinning CH and the
  ℵ₁-vs-𝔠 statements to `Cardinal.{0}`.
