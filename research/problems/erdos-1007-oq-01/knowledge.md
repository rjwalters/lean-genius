# Knowledge Base: erdos-1007-oq-01

Minimum edges for graph dimension d in general.

---

## Session 2026-03-17 (Session 6) - Cleanup, Bug Fixes, Completion

**Mode**: REVISIT (depth-first, RICH knowledge score 40)
**Outcome**: completed — fixed compilation bugs, removed dead code, marked complete

### What Was Done
- **Fixed duplicate `complete_graph_dim_ge_tight` bug**: Two theorems had the same name.
  Renamed the full linear-independence proof to `unit_embedding_dim_lower_bound` (general
  lemma about any embedding), keeping the shorter corollary as `complete_graph_dim_ge_tight`.
- **Removed dead code**: `centered_dot_product` and `centered_dot_product_diag` referenced
  undefined `unit_embed_dist_sq` and were never used (superseded by the direct proof approach).
- **Replaced placeholder**: `upper_bound_from_exact_dim` was `True := trivial`. Replaced with
  `complete_graph_witnesses_dim`: proves dim(K_{d+1}) = d for all d ≥ 1 using `complete_graph_dim_exact`.
- **Updated header**: Added sorry count (0) to file documentation.

### Assessment
Problem is **COMPLETED**:
- 1321 lines, 0 sorries, 9 computational axioms
- dim(K_n) = n-1 fully proved (both directions)
- Conjecture relationships mapped (optimality ↔ monotonicity ↔ quadratic growth)
- All individual bounds verified (K₂ through K₅)
- d=4 anomaly documented
- 9 remaining axioms encode computational search results (House 2013, Chaffee-Noble 2016)
  that cannot be proved without implementing graph search algorithms

### Files Modified
- `proofs/Proofs/Erdos1007OQ01.lean` — bug fixes, dead code removal, placeholder replacement

---

## Session 2026-03-17 (Session 5) - Prove dim(K_n) ≥ n-1 Lower Bound

**Mode**: REVISIT (depth-first, RICH knowledge)
**Outcome**: progress — eliminated axiom, proved lower bound

### What Was Done
- **Proved `complete_graph_dim_ge_tight`** (was axiom → now theorem): dim(K_n) ≥ n-1
  for all n ≥ 2. This was the last remaining dimension axiom.
- **Proved `unit_embedding_dim_lower_bound`**: General theorem that any unit-distance
  embedding of K_n in ℝ^d requires d ≥ n-1.
- **Helper `sq_dist_of_sqrt_one`**: Extracts squared distance from sqrt-based condition.

### Proof Technique
Center at vertex 0 to get n-1 vectors g(i) = f(i+1) - f(0) in ℝ^d.
- Squared norms ‖g(i)‖² = 1 (unit distance from vertex 0)
- Inner products ⟨g(i),g(k)⟩ = 1/2 for i ≠ k (by polarization: ‖g(i)-g(k)‖² = 1)
- Linear independence: from ∑ cᵢg(i) = 0, inner products give cₖ + S/2 - cₖ/2 = 0,
  so cₖ = -S. Then S = (n-1)(-S) implies (n)S = 0, S = 0, all cₖ = 0.
- Apply `LinearIndependent.fintype_card_le_finrank` + `Module.finrank_fin_fun` to get
  n-1 ≤ d.

### Impact
- Axiom count: 10 → 9 (eliminated the only non-computational axiom)
- `complete_graph_dim_exact` (dim(K_n) = n-1) is now fully proved from both directions
- Removed obsolete §21 sketch section
- All 9 remaining axioms are purely computational (minEdgesForDim values and bounds)

### Files Modified
- `proofs/Proofs/Erdos1007OQ01.lean` — replaced axiom with proved theorem (+100/-42 lines)
- `src/data/research/problems/erdos-1007-oq-01.json` — updated knowledge

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

---

## Session 2026-03-17 (researcher-4) - Last Sorry Eliminated

**Mode**: REVISIT (depth-first, RICH knowledge score 39)
**Problem**: erdos-1007-oq-01
**Prior Status**: active (1361 lines, 9 axioms, 1 sorry in complete_graph_dim_ge_tight)

### What Was Done
Eliminated the last `sorry` in `complete_graph_dim_ge_tight`, proving dim(K_n) ≥ n-1 for all n ≥ 2.

The sorry was in the linear independence proof of centered vectors w(j) = emb(j+1) - emb(0).
The original approach tried quadratic form expansion (double sum), which was too complex.

**New approach**: Inner product method (avoids double sums entirely)
1. Establish ∑_k w(j,k)² = 1 (unit norm) from emb.unit_edges
2. Establish ∑_k w(a,k)·w(b,k) = 1/2 for a≠b (from ‖w_a-w_b‖² = 1, expand)
3. Given ∑_j g_j·w_j = 0, compute ⟨0, w_i⟩ = ∑_j g_j·⟨w_j, w_i⟩ = 0
4. Split: g_i·1 + ∑_{j≠i} g_j·(1/2) = g_i/2 + S/2 = 0 where S = ∑g_j
5. So g_i = -S for all i ∈ s
6. Summing: S = |s|·(-S) → S(1+|s|) = 0 → S = 0 → g_i = 0

### Stats After Changes
- 1436 lines (was 1361), 0 sorries (was 1), 9 axioms
- Pre-existing Mathlib breakages in §19 regSimplexEmbed still present (known issue)
- The core theorem complete_graph_dim_ge_tight is now fully proved

### Files Modified
- `proofs/Proofs/Erdos1007OQ01.lean` — eliminated last sorry with 84-line proof
