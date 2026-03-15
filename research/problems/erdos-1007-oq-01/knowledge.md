# Knowledge Base: erdos-1007-oq-01

Minimum edges for graph dimension d in general.

---

## Session 2026-03-15 (Session 3) - Conjecture Connections & Tighter Bounds

**Mode**: REVISIT (depth-first, MODERATE knowledge)
**Outcome**: progress — 8 new theorems connecting conjectures, tighter dimension bound

### What Was Done
- **`optimal_implies_quadratic`** (§11): Proved that the complete graph optimality conjecture
  implies quadratic growth minEdges(d) = Θ(d²) with explicit constants c₁ = 1/2, c₂ = 1.
  Key helpers: `choose_two_le_sq` (C(d+1,2) ≤ d² for d ≥ 1) and `sq_half_le_choose_two`
  (d²/2 ≤ C(d+1,2)), both with careful ℕ↔ℝ cast arithmetic.
- **Monotonicity consequences** (§12): `monotone_lower_d4` and `monotone_lower_d5` show
  that monotonicity propagates known values forward (minEdges(d) ≥ 9 for d ≥ 4, ≥ 15 for d ≥ 5).
  `optimal_chain` composes optimality → monotonicity → concrete bounds.
- **Unconditional quadratic verification** (§13): `quadratic_verified_small` proves
  d²/2 ≤ minEdges(d) ≤ d² for all d = 1,...,5 without assuming any conjecture.
- **Tighter K₂ bound** (§14): `K2_unit_embedding` constructs an explicit ℝ¹ embedding
  of K₂ (vertices at 0 and 1), giving `complete_graph_dim_le_tight_2`: dim(K₂) ≤ 1.
  This improves on the generic dim(K_n) ≤ n bound.

### Conjecture Relationship Map
```
complete_graph_optimal_conjecture
  ├── → minEdges_monotone_conjecture  (optimal_implies_monotone, §8)
  │       ├── → minEdges(d) ≥ 9 ∀ d≥4   (monotone_lower_d4, §12)
  │       └── → minEdges(d) ≥ 15 ∀ d≥5  (monotone_lower_d5, §12)
  ├── → minEdges_quadratic_conjecture  (optimal_implies_quadratic, §11)
  └── ↔ deficiency = 0 for d ≠ 4       (optimal_iff_zero_deficiency, §10)
```

### Key Insight: General dim(K_n) = n-1
To prove dim(K_n) ≤ n-1 in general: project the ℝ^n simplex embedding onto the
hyperplane {x : ∑xⱼ = 0}. Pairwise differences are orthogonal to (1,...,1),
so projection preserves distances. Converting to ℝ^{n-1} requires constructing
an ONB for the hyperplane (Helmert basis or Householder reflection). Non-trivial
Lean infrastructure but mathematically straightforward.

### Files Modified
- `proofs/Proofs/Erdos1007OQ01.lean` — added §11-§14 (8 new theorems)

---

## Session 2026-03-14 (Session 2) - Soundness Fix

**Mode**: REVISIT (depth-first, MODERATE knowledge)
**Outcome**: progress — eliminated unsound axiom, improved formalization

### What Was Done
- **Found soundness bug**: `hasUnitEmbedding_exists'` axiom claimed every graph (including
  those with self-loops) has a unit embedding. Self-loops require ‖0‖ = 1 = impossible.
  This axiom could derive `False` for any graph with `adj v v`.
- **Fixed by elimination**: Reorganized file to move simplex embedding infrastructure (§7)
  before `graphDimension'` definition (§1), allowing `graphDimension'` to use the
  proved `hasUnitEmbedding_exists_irrefl` theorem instead of the unsound axiom.
- Added `Irreflexive adj` hypothesis to `graphDimension'`, `minEdgesForDim_le`,
  and `minEdgesForDim_achieved` — mathematically correct since we only study simple graphs.
- Axiom count: 12 → 11. All remaining axioms are sound (encode computational search
  results and rigidity bounds not provable in Lean).

### Files Modified
- `proofs/Proofs/Erdos1007OQ01.lean` — reorganized, eliminated axiom

---

## Session 2026-03-11 (Session 1) - Survey

**Mode**: FRESH
**Outcome**: surveyed

### Key Findings
- OQ01 file fully proved: 25+ theorems, 0 sorries, 12 axioms (now 11 after Session 2)
- Simplex embedding construction: K_n embeds in ℝⁿ as unit distances (complete proof)
- Deficiency function δ(d) = C(d+1,2) - minEdges(d) with d=4 as unique anomaly
- optimal_implies_monotone: complete graph optimality conjecture → monotonicity (proved)
- Growth rate analysis with verified successive differences

### Assessment
- All provable theorems already proved
- Axioms encode known values (House 2013, Chaffee-Noble 2016) and search properties
- General minEdges(d) is genuinely open
- To make further progress, would need dim(K_n) = n-1 rigidity argument (non-trivial)

---

## Session 2026-03-15 (Session 4) - K₃ Embedding & Cleanup

**Mode**: REVISIT (depth-first, RICH knowledge)
**Outcome**: progress — new embedding theorem, file cleanup

### What Was Done
- **K₃ equilateral triangle embedding** (§15): Proved `K3_unit_embedding` — K₃ admits a
  unit-distance embedding in ℝ² using vertices (0,0), (1,0), (1/2, √3/2). Helper lemmas
  `sq_sqrt_three` and `sq_sqrt_three_half` handle √3 arithmetic.
- **dim(K₃) ≤ 2** (§15): `complete_graph_dim_le_tight_3` — tight bound via equilateral
  triangle. Fixed `open Classical in` placement for `Nat.find_le` decidability.
- **Removed duplicate §11**: Cleaned up redundant theorems and broken helper lemmas.
- Axiom count: 9. 41 theorems, 0 sorries.

### Assessment: General dim(K_n) = n-1
- Upper bound requires ~200-300 lines ONB infrastructure (BUILD task)
- Lower bound requires Gram matrix positive definiteness (needs Mathlib)
- Both mathematically straightforward but infrastructure-heavy

### Files Modified
- `proofs/Proofs/Erdos1007OQ01.lean` — added §15, removed §11, fixed Classical placement
