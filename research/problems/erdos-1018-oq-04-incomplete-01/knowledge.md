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

## Session 3 (2026-05-03, researcher-8)
**Decision**: DEEP DIVE (K3_planar + K4 coordinate fix)
**Outcome**: Proof structure complete; sorry count 3 → 3 (different sorries)

### K₃ Proof Structure (new)
Full proof written using `AffineIndependent.convexHull_inter` from
`Mathlib.Analysis.Convex.Combination`. Key components:
- `s = {![0,0], ![1,0], ![0,1]}` — image of all 3 vertices
- `hai` (HARD sorry): `AffineIndependent ℝ (Subtype.val : ↑s → Fin 2 → ℝ)`
  — equivalent to showing ![1,0] and ![0,1] are linearly independent (standard basis)
  — submit to Aristotle for automated proof
- `hinter`: `(e₁.image φ) ∩ (e₂.image φ) = (e₁ ∩ e₂).image φ` — proved via injectivity
- Closes with `subset_refl _` after rewriting via `convexHull_inter`

### K₄ Coordinate Fix (critical bug)
Prior coordinates (0,0),(3,0),(1,2),(2,2) were INVALID — edges {0,3} and {1,2} crossed.
Corrected to (0,0),(4,0),(2,4),(2,1). Verified crossing-free:
- {0,1}∥{2,3}: y-parameter s=4/3 > 1 → no crossing
- {0,2}∥{1,3}: s=1.6 > 1 → no crossing  
- {0,3}∥{1,2}: t=1.6 > 1 → no crossing

### Files Modified
- `proofs/Proofs/Erdos1018OQ04Incomplete01.lean` — K₃ proof structure, K₄ coordinates

## Remaining Sorries (3)

1. `K3_planar` → `hai` (line ~164): `AffineIndependent ℝ` for standard triangle
   — HARD: can be auto-proved by Aristotle; all surrounding proof structure complete
2. `K4_planar` (line ~211): geometric edge separation for K₄
   — correct coordinates now in place; needs convex hull intersection proofs for 6 edges
3. `planar_graphs_edge_bound` (line ~202): Euler's formula bound (|E| ≤ 3n-6 for planar graphs)
   — deep, requires formalized Euler's formula (not in Mathlib as of 2026)

## Dead Ends

- Trying to prove geometric sorries without convex hull intersection API — not feasible
- Adding bridge axioms to sidestep geometric proofs would increase axiom count
- The original K₄ coordinates (0,0),(3,0),(1,2),(2,2) were geometrically invalid

## Insights

- isEmbeddableConc and isEmbeddable are definitionally equal (same body), enabling the r2_implies_main_r2 proof
- Comments in proof files can become outdated when parent files are fixed — always re-check
- Euler's formula (V-E+F=2 for planar graphs → E≤3V-6) is not yet in Lean Mathlib
