# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T12:30:00-07:00
**Iteration**: 4

## Current Focus
The **n=1 line is now COMPLETE end-to-end**. This session added the *continuous
capstone*: `proofs/Proofs/SpernerTuckerBorsukUlamOneDim.lean` (117 LOC, 0 sorries,
0 axioms) carries out the **Tucker ⟹ Borsuk–Ulam** reduction in dimension 1. In
dim 1 the usual mesh→0/compactness limit collapses to the **Intermediate Value
Theorem**, giving the genuine *continuous* **1-D Borsuk–Ulam theorem**:
`borsuk_ulam_circle` — a continuous 1-periodic `f : ℝ → ℝ` (a function on the
circle) takes **equal values at some antipodal pair** `c`, `c + 1/2`.

Together with the prior `SpernerTuckerOneDim.lean` (discrete combinatorial core,
merged PR #30823) this gives the full discrete→continuous n=1 story.

## Verification note
Docker IMAGE build is currently broken (containerd `meta.db` I/O error), but
`docker ps` works. Verified the new file via the established fallback
`lake env lean` against the main-repo Mathlib `.olean` cache (0 errors;
`#print axioms` = only propext/Classical.choice/Quot.sound).

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
- n>=2 Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (the genuine analytic
  phase; in dim 1 this was discharged this session by IVT).
