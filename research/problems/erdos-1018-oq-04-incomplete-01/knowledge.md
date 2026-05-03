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

`r2_implies_main_r2` proved by definitional equality — `isEmbeddableConc` and `isEmbeddable`
have identical bodies, so exact-proof works. `criticalDim 2 = 2`.

### Session 3 (2026-05-03, researcher-7)
**Decision**: DEEP DIVE (K3_planar + K4_planar)
**Outcome**: -2 sorries (3→1)

**K3_planar** (coords 0=(0,0), 1=(1,0), 2=(0,1)):
- All 3 edge pairs adjacent — K₃ has no non-adjacent pairs
- `proj_const` helper: if f is linear and constant cv on vertex images, then f=cv on hull
- 6 cases (3 pairs × 2 orderings): {0,1}∩{0,2}: y=0∧x=0→(0,0); {0,1}∩{1,2}: y=0∧x+y=1→(1,0); {0,2}∩{1,2}: x=0∧x+y=1→(0,1)

**K4_planar** (corrected coords 0=(0,0), 1=(2,0), 2=(1,2), 3=(1,1)):
- Bug fix: original (3,0) caused {0,3}/{1,2} to cross at (3/2,3/2)
- Vertex 3=(1,1) placed inside triangle 0-1-2
- 30 cases: 24 adjacent (proj_const) + 6 non-adjacent (plb/pub):
  - {0,1}/{2,3}: y=0 vs y≥1 → contradiction
  - {0,2}/{1,3}: 2x-y=0 + x+y=2 + x≥1 → 3x=2 contradiction
  - {0,3}/{1,2}: 2x+y≤3 vs 2x+y=4 → contradiction

## Remaining Sorries (1)

1. `planar_graphs_edge_bound`: Euler formula bound E≤3V-6 for planar graphs
   — not in Lean Mathlib as of May 2026

## Dead Ends

- Original K₄ coordinates (0,0),(3,0),(1,2),(2,2): edges {0,3}/{1,2} CROSS at (3/2,3/2)
- Trying geometric sorries without convex hull theory — not feasible

## Insights

- isEmbeddableConc and isEmbeddable are definitionally equal (same body)
- Comments in proof files can become outdated when parent files are fixed — always re-check
- Euler's formula (V-E+F=2 → E≤3V-6) is not yet in Lean Mathlib (May 2026)
- proj_const/proj_lb/proj_ub helpers (linear functionals + convexHull_min) suffice for K3/K4
- For non-adjacent edge separation: find f with f=cv on one hull, f≥/≤c' on other
- K₄ non-adjacent pairs: exactly 3 ({0,1}/{2,3}, {0,2}/{1,3}, {0,3}/{1,2})
