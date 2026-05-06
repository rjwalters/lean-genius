# Problem: Brouwer's Fixed-Point Theorem via Sperner's Lemma

**Pool ID**: sperner-ndim-mathlib-oq-02  
**Status**: in-progress  
**Phase**: ACT

## Summary

Prove Brouwer's fixed-point theorem for Δⁿ = {x : Fin(n+1) → ℝ | ∀i, xᵢ ≥ 0, Σxᵢ = 1}
using the combinatorial Sperner's lemma approach (SpernerNDimMathlib.lean, 0 axioms).

The key insight: for f: Δⁿ → Δⁿ, define the Sperner coloring c(v) = min{i ∈ supp(v) : f(v)ᵢ ≤ vᵢ}.
This is well-defined (proved algebraically) and satisfies the Sperner boundary condition (proved).
The existence of a fixed point then follows from Sperner's lemma + compactness.

## Session 2026-05-06 (Session 1) — Initial formalization

**Mode**: FRESH  
**Outcome**: progress

### What I Did

- Branched `feature/researcher-11-sperner-ndim-mathlib-oq-02` from origin/main
- Created `proofs/Proofs/SpernerNDimMathlibOQ02.lean` (254 lines, 0 sorries, 2 axioms)
- Created gallery entry `src/data/proofs/sperner-ndim-mathlib-oq-02/` (meta.json, index.ts, annotations.json)
- Added entry to `src/data/proofs/listings.json`
- PR pending Docker build

### Key Findings

- **Coloring well-definedness is purely algebraic**: if f(v)ᵢ > vᵢ for all i ∈ supp(v), and 0 ≤ f(v)ᵢ for i ∉ supp(v), then Σf(v)ᵢ > Σvᵢ = 1. Proved by `Finset.sum_lt_sum`.
- **Boundary condition follows trivially**: c(v) ∈ supp(v) by definition, so vⱼ = 0 → j ∉ supp(v) → c(v) ≠ j.
- **2 axioms are sufficient**: (1) grid triangulation + Sperner → near-fixed-point, (2) compactness → exact fixed point.
- **Fundamentally different from algebraic topology approach**: avoids homology theory entirely.

### Files Modified

- `proofs/Proofs/SpernerNDimMathlibOQ02.lean` (new)
- `src/data/proofs/sperner-ndim-mathlib-oq-02/` (new)
- `src/data/proofs/listings.json` (entry added)
- `src/data/research/problems/sperner-ndim-mathlib-oq-02.json` (knowledge updated)

### Next Steps

1. Eliminate `sperner_near_fixed_point` axiom: build the grid CellComplex for Δⁿ
   - Vertices: (a₀/N,...,aₙ/N) with Σaᵢ = N, aᵢ ∈ ℕ
   - Simplices: ordered chains with constant "miss" direction
   - Must fix boundary_doors_odd (broken in SpernerGrid.lean due to double-representation)
   - Estimated: ~200 lines
2. Eliminate `fixed_point_from_approx` axiom: use Mathlib's `IsCompact.tendsto_subseq`
   - Δⁿ is compact in Lean via `Matrix.stdSimplex` infrastructure
   - Need `tendsto_nhds_unique` + `ContinuousOn` machinery
   - Estimated: ~100 lines
3. Submit OQ-01 axioms (swapAdj_nodup, swapAdj_prefixSet_eq, swapAdj_ne_self) to Aristotle
