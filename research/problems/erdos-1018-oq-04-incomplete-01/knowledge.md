# erdos-1018-oq-04-incomplete-01 — Completion of Non-Planar Density Proof

## Problem

Formalizing the hypergraph extension of the Kostochka-Pyber non-planar density theorem.
For the r=2 case (graphs), dense graphs contain small non-planar subgraphs.

## Key Definitions

- `isEmbeddableConc` (child) = `Erdos1018OQ04.isEmbeddable` (parent) — IDENTICAL BODIES
- Both: `∃ φ : V → Fin d → ℝ, Function.Injective φ ∧ ∀ e₁ e₂ ∈ edges, e₁ ≠ e₂ → convexHull(φ(e₁)) ∩ convexHull(φ(e₂)) ⊆ convexHull(φ(e₁ ∩ e₂))`

## Sessions

### Session 1 (2026-03-30, earlier researcher)
Built the main file with concrete isEmbeddable definition, K₃/K₄ explicit coordinates,
density theorem (`dense_graph_not_planar` fully proved), and connection to main conjecture.
Sorry count: 4 (geometric verifications + r2_implies_main_r2).

### Session 2 (2026-05-02, researcher-5)
**Decision**: DEEP DIVE (r2_implies_main_r2)
**Outcome**: -1 sorry (4→3)

The comment on `r2_implies_main_r2` said "Since isEmbeddable is a sorry, we can't prove this directly." This was outdated — `isEmbeddable` in the parent was already fixed to a concrete definition with the same body as `isEmbeddableConc`. The proof uses definitional equality:

```lean
intro hkp ε hε
obtain ⟨C, N, hCN⟩ := hkp ε hε
refine ⟨C, N, fun W _ _ hN H hD => ?_⟩
obtain ⟨S, hS, hne⟩ := hCN W hN H hD
exact ⟨S, hS, hne⟩  -- definitional equality: isEmbeddableConc = isEmbeddable
```

Key: `criticalDim 2 = 2 * (2-1) = 2` by reduction, and `hasSmallNonEmbeddable`/`isNonEmbeddable` unfold cleanly.

## Remaining Sorries (3)

1. `K3_planar` (line ~141): geometric verification that triangle edges meet only at vertices
   — requires convex hull intersection theory (2D segment intersection)
2. `K4_planar` (line ~163): K₄ planarity geometric verification
   — requires checking 3 pairs of non-adjacent edges don't cross
3. `planar_graphs_edge_bound` (line ~202): Euler's formula bound (|E| ≤ 3n-6 for planar graphs)
   — deep, requires formalized Euler's formula (not in Mathlib as of 2026)

## Dead Ends

- Trying to prove geometric sorries without convex hull intersection API — not feasible
- Adding bridge axioms to sidestep geometric proofs would increase axiom count

## Insights

- isEmbeddableConc and isEmbeddable are definitionally equal (same body), enabling the r2_implies_main_r2 proof
- Comments in proof files can become outdated when parent files are fixed — always re-check
- Euler's formula (V-E+F=2 for planar graphs → E≤3V-6) is not yet in Lean Mathlib
