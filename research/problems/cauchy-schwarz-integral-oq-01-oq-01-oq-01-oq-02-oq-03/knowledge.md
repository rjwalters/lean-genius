# cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-03 — Knowledge Base

## Problem

Does the power mean chain HM ≤ GM ≤ AM ≤ QM (proved in the parent file for equal weights) 
generalize to weighted means WHM ≤ WGM ≤ WAM ≤ WQM for weights w₁, w₂ > 0 with w₁ + w₂ = 1?

Weighted definitions:
- WHM(a,b) = (w₁/a + w₂/b)⁻¹
- WGM(a,b) = a^w₁ · b^w₂
- WAM(a,b) = w₁·a + w₂·b
- WQM(a,b) = √(w₁·a² + w₂·b²)

---

## Session 2026-05-04 (Session 1) - Weighted Chain Proof

**Mode**: FRESH
**Outcome**: completed — 11 theorems, 4 defs, 0 sorries, 0 axioms

### What I Did
- Identified problem as natural extension of power mean chain (parent: CauchySchwarzIntegralOQ01OQ01OQ01OQ02)
- Wrote full proof in CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ03.lean
- Three-step chain with distinct techniques:
  1. **WGM ≤ WAM**: One-liner via `Real.geom_mean_le_arith_mean2_weighted`
  2. **WAM ≤ WQM**: Jensen via identity w₁a² + w₂b² - (w₁a + w₂b)² = w₁w₂(a-b)²
  3. **WHM ≤ WGM**: Apply WGM ≤ WAM to (1/a, 1/b), flip via `inv_le_comm₀`
- Added specialization theorems showing equal-weights recovers unweighted chain
- Created gallery entry with full meta.json

### Key Findings
- `Real.geom_mean_le_arith_mean2_weighted hw₁ hw₂ ha hb hw` is the central tool
- Jensen identity proved by `w₂ = 1 - w₁` substitution then `ring` — no manual hints
- `inv_le_comm₀ hx hy : x⁻¹ ≤ y ↔ y⁻¹ ≤ x` is the reciprocal-inversion tool (for x, y > 0)
- The WHM ≤ WGM proof is the most interesting: apply AM-GM to (1/a, 1/b), get WGM⁻¹ ≤ WHM⁻¹, then flip

### Files Created/Modified
- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ03.lean` (176 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-03/meta.json` (new gallery entry)
- `src/data/research/problems/cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-03.json` (updated knowledge)

### Next Steps
- Docker build verification pending
- Open question: general M_r^w ≤ M_s^w monotonicity for all r ≤ s (requires Jensen for convex f)
