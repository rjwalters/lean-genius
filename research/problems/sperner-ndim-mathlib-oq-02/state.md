# Current State

**Phase**: ACT
**Since**: 2026-05-06T18:16:19+03:00
**Iteration**: 3

## Current Focus

1 axiom remaining: `sperner_near_fixed_point` — connecting grid triangulation to abstract Sperner.
All other components are fully proved (0 sorries). PR #16235 is open.

## Active Approach

Sperner coloring: c(v) = min{i ∈ supp(v) : f(v)_i ≤ v_i}
- Well-definedness: algebraic (Finset.sum_lt_sum), PROVED
- Boundary condition: c(v) ∈ supp(v), PROVED
- Compactness → exact fixed point (fixed_point_from_approx): PROVED
- Main theorem: from 1 axiom, PROVED

## Blocker: Grid Triangulation

`sperner_near_fixed_point` requires building a `SpernerTriangulation n N` (from SpernerNDim.lean)
for the Nth Freudenthal subdivision of Δⁿ, then proving:
1. `IsSperner (spernerColorMap f hf_map)` — follows from existing `spernerColorMap_boundary`
2. `Odd (boundary doors on face d)` — requires inductive argument via restriction to face d

The inductive argument:
- Boundary doors on face d ↔ FC (n-1)-simplices on the restriction to face d (Δⁿ⁻¹)
- By induction, FC (n-1)-simplices are odd → boundary doors on face d are odd
- Base case (n=0): Δ⁰ = {point}, trivial

The concrete triangulation type needs:
- `Simplex` type: canonical representative for each geometric simplex (avoiding double-counting)
- `adj`: correct adjacency for the Freudenthal subdivision
- `boundary_face` axiom: on face k boundary, non-k vertices satisfy onFace k
- `adj_unique_facet`: two faces of s can't both be adjacent to same neighbor

SpernerGrid.lean's approach is BROKEN (double-counts simplices with different miss directions).
Canonical fix: use (base, σ) where σ is a permutation of Fin(n+1) with the last element
being the canonical "miss" direction, and canonical ordering.

Alternative approaches considered:
- KKM approach: n-dim KKM not in Mathlib; would need ~same effort to prove
- Schauder: available in gallery but not the intended proof strategy (OQ-02 is specifically via Sperner)
- IVT for n=1: gives exact fixed point for n=1 but doesn't extend to higher n

## Next Action

Build canonical Freudenthal `SpernerTriangulation` (~400 lines):
1. `GridSimplex n N` = pair of (base : Fin(n+1) → ℕ with Σ=N, σ : Equiv.Perm (Fin(n+1)))
2. `gridAdj`: adjacency where face k of simplex (base, σ) is adjacent to (base', σ') obtained
   by swapping the order of steps k-1 and k (the local transposition)
3. `gridBoundaryFace`: adj = none iff the geometric face is on the boundary of Δⁿ
4. Restriction to face d: map (base, σ) on face d → (n-1)-simplex for induction

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1 (Sperner + compactness, now 1 axiom remaining)
