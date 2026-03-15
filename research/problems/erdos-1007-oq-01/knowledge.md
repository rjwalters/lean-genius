# Knowledge Base: erdos-1007-oq-01

Minimum edges for graph dimension d in general.

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
