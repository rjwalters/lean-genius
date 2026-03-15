# Knowledge Base: erdos-1007-oq-01

Minimum edges for graph dimension d in general.

---

## Session 2026-03-15 (Session 3) - Conjecture Relationship

**Mode**: REVISIT (depth-first, MODERATE knowledge)
**Outcome**: progress — proved new structural theorem

### What Was Done
- **Proved `optimal_implies_quadratic`**: If the complete graph optimality conjecture holds
  (K_{d+1} optimal for d ≠ 4), then minEdges(d) = Θ(d²) with explicit constants c₁ = 1/2, c₂ = 1.
  - Lower bound: d²/2 ≤ d(d+1)/2 since d ≤ d+1. For d=4: 8 ≤ 9.
  - Upper bound: d(d+1)/2 ≤ d² since d+1 ≤ 2d for d ≥ 1. For d=4: 9 ≤ 16.
- Added helper `choose_succ_two_real` for Nat/Real casting of C(d+1,2).
- File now proves THREE conjecture implications from `complete_graph_optimal_conjecture`:
  1. → monotonicity (`optimal_implies_monotone`)
  2. → quadratic growth (`optimal_implies_quadratic`) [NEW]
  3. ↔ zero deficiency (`optimal_iff_zero_deficiency`)

### Files Modified
- `proofs/Proofs/Erdos1007OQ01.lean` — added optimal_implies_quadratic

### Assessment
- All provable theorems now proved (0 sorries, 11 axioms)
- The complete graph optimality conjecture is identified as the key hypothesis:
  it implies both monotonicity and quadratic growth
- Remaining axioms encode computational search results (dim0-dim5 values) and
  structural properties (lower/upper bounds, minEdgesForDim definition) that
  require either exhaustive graph search or rigidity theory infrastructure
- To make further progress: need dim(K_n) = n-1 rigidity (substantial linear algebra)

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
