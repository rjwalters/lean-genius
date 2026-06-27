# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T10:30:00-07:00
**Iteration**: 3

## Current Focus
n=1 Tucker milestone SHIPPED and verified (Docker is up — prior blocker cleared).
New file `proofs/Proofs/SpernerTuckerOneDim.lean` (169 LOC, 0 sorries, 0 axioms)
proves 1-D Tucker = the combinatorial core of 1-D Borsuk–Ulam via a direct
sign-change parity (discrete fundamental theorem of calculus over `ZMod 2`).

## Active Approach
Direct sign-change parity, not a `CellComplex` instantiation (the engine's
panchromatic conclusion diverges from the complementary-edge target — Insight 1).
- `complementary_count_cast`: #complementary-edges ≡ `lam 0 + lam (last)` (mod 2).
- `tucker_one_dim`: antipodal boundary ⟹ odd count.
- `exists_complementary_edge`: 1-D Tucker existence.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2 (engine-reusability assessment → direct-parity port)

## Blockers
- None for n=1 (done).
- n>=2 Tucker engine is substantial (~500-1000+ LOC: path-following on
  almost-complementary simplices, antipodal pairing of boundary path-endpoints).

## Next Action
- n>=2: scope/build the Freund-Todd / Prescott-Su path-following engine (the
  complementary-edge count is NOT a parity invariant for n>=2 — Insight 3), or the
  Tucker-via-Sperner doubling/quotient reduction on RP^n.
- Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (separate analytic phase).
