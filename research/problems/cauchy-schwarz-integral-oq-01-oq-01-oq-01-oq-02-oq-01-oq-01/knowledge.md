# Power Mean Equality: M_r = M_s iff All Elements Equal

**Problem ID**: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01
**Parent**: cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01 (Full Power Mean Monotonicity)

## Problem Statement

For positive weights w summing to 1 and positive reals z, and 0 < r < t:

  M_r(z, w) = M_t(z, w) iff all z_i are equal.

Where M_r = (Σ w_i z_i^r)^(1/r) is the weighted power mean of order r.

## Session 2026-05-07 (Session 1) — Complete Proof

**Mode**: FRESH
**Outcome**: completed — full proof written, gallery entry created

### What I Did

1. Identified this problem as the top-tractability available problem (tractability 6)
2. Verified that Mathlib has exactly the right infrastructure:
   - `strictConvexOn_rpow` (SpecificFunctions.Basic): x ↦ x^p strictly convex for p > 1
   - `StrictConvexOn.map_sum_lt` (Jensen.lean): strict Jensen inequality
   - `Real.rpow_left_inj` (Pow.Real): injectivity of x ↦ x^p for p ≠ 0
3. Confirmed that Mathlib's MeanInequalitiesPow.lean explicitly marks this as TODO (line 36)
4. Wrote complete proof: 200 lines, 0 sorries, 0 axioms
5. Created gallery entry with meta.json

### Key Findings

- The clean proof strategy uses strict Jensen CONTRADICTION rather than Jensen equality characterization
- M_r = M_t → raise to power t → A^(t/r) = B; if z_j ≠ z_k then strict Jensen gives A^(t/r) < B
- Bridge between Mathlib's smul-based Jensen API and our mul-based formulas: `simp only [smul_eq_mul]`
- `Real.rpow_mul` and `field_simp` handle all the algebraic manipulations cleanly

### Files Modified

- `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01.lean` (created, 200 lines)
- `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01/meta.json` (created)
- `research/problems/cauchy-schwarz-integral-oq-01-oq-01-oq-01-oq-02-oq-01-oq-01/knowledge.md` (this file)

### Build Status

Docker build succeeded: 3059 jobs, 0 errors, 0 sorries. Two Lean 4.26 API drift
issues were fixed:

1. `AmgmInequalityOQ03.lean`: trailing `/--` docstring at EOF caused "unexpected
   end of input; expected 'lemma'" — changed to plain `/-` block comment.
2. `CauchySchwarzIntegralOQ01OQ01OQ01OQ02OQ01OQ01.lean`: `lt_div_iff` and
   `div_lt_div_right` removed in Lean 4.26 — replaced with a stable calc proof
   using `mul_inv_cancel₀ + mul_lt_mul_of_pos_right + div_eq_mul_inv`.

### PR

#16419 open, labeled `research`, ready for deployer to merge.

### Phase: COMPLETED
