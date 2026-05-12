# Mean Value Theorem OQ-02 / OQ-04 / OQ-01: Refutation of the OQ-04 axiom

## Problem Summary

**Slug**: `mean-value-theorem-oq-02-oq-04-oq-01`
**Tier**: B (NEW-PROBLEM SCAFFOLD pattern)
**Significance**: 7
**Tractability**: 6
**Phase**: ACT (Lean code shipped, refutation complete, S2-deferred sorry)

**Question (from candidate-pool note)**: Can the axiom `analytic_taylor_remainder_uniform_bound` be proved by S2 via Mathlib's `HasFPowerSeriesOnBall` infrastructure? The key Mathlib lemma is a Cauchy coefficient bound `‖p k‖ ≤ M / R^k`; the rest is the geometric tail estimate.

**Answer (Session 1)**: NO. The parent axiom is mathematically false as stated.

## Session 2026-05-12 (Session 1, FRESH) — Refutation by Runge counterexample

**Mode**: FRESH (NEW-PROBLEM SCAFFOLD pattern; tier-B fallback after MODERATE+ saturation)
**Outcome**: progress (axiom refuted constructively; corrected statement deferred to S2)

### What I Did

1. **Investigated the parent axiom**. Read `Proofs/MeanValueTheoremOQ02OQ04.lean`, identified the OQ-04 axiom statement: for `f : ℝ → ℝ` real-analytic on `(a-R, a+R)` with `|f y| ≤ M` on that interval, conclude `|f x − T_n f(a)(x)| ≤ M·r^(n+1) / (R-r)`. The parent's docstring explicitly references the COMPLEX disk in the "mathematical background" but axiomatizes only the REAL-interval version, "absorbing the R^n into M".

2. **Identified counterexample by mental check**. The Runge function `f(x) = 1/(1+x²)` is real-analytic on ℝ, bounded by 1, but has complex poles at ±i. The complex Cauchy radius around 0 is only 1, NOT R = 100. At `(a, R, M, r, n, x) = (0, 100, 1, 1, 0, 1)`:
   - LHS: `|f(1) − f(0)| = |1/2 − 1| = 1/2`
   - RHS: `1·1^1 / (100−1) = 1/99 ≈ 0.0101`
   - **50× gap** — robust refutation.

3. **Probed Mathlib API**. Confirmed via `/Users/rwalters/Projects/lean-genius-proofs/.lake/packages/mathlib/Mathlib/Analysis/Analytic/`:
   - `analyticOn_id ℝ : AnalyticOn ℝ (fun x ↦ x) s` (note: 𝕜 is EXPLICIT)
   - `analyticOn_const : AnalyticOn 𝕜 (fun _ ↦ v) s` (𝕜 implicit)
   - `AnalyticOn.pow`, `AnalyticOn.add`, `AnalyticOn.div` (with nonzero hypothesis)
   - `HasFPowerSeriesOnBall.uniform_geometric_approx'` for the existential approximation
   - `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius` for explicit Cauchy bounds

4. **Wrote Lean file** `Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` (~280 lines):
   - §1: Defined `runge x := 1/(1+x²)`, proved `runge_one_add_sq_pos`, `runge_abs_le_one`, `runge_zero`, `runge_one`, `runge_analyticOn_R`.
   - §2: Defined `OQ04_AxiomStatement : Prop` to capture the parent axiom's signature, then proved `oq04_axiom_is_false` and `oq04_parent_axiom_is_false_in_principle` via specialization at the Runge witness.
   - §3: Stated `analytic_taylor_remainder_uniform_bound_complex` (corrected complex-disk version) with sorry, deferred to S2 with explicit Mathlib chain documented.

5. **Fixed grandparent build drift**. The build initially failed because `Proofs/MeanValueTheoremOQ02.lean` line 56 used the deprecated `∑ k in Finset.range ...` syntax (Mathlib has switched to `∑ k ∈ ...`). Single-character fix unblocks the entire MVT-OQ02 subtree (3 downstream files: `AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle.lean`, `MeanValueTheoremOQ02OQ04.lean`, this file).

6. **Created gallery scaffold**:
   - `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/{meta.json, index.ts, annotations.json}`
   - `src/data/research/problems/mean-value-theorem-oq-02-oq-04-oq-01.json`
   - This `knowledge.md` and `state.md`

### Key Findings

- **The parent OQ-04 axiom is mathematically false**: `f(x) = 1/(1+x²)` at `(R, M, r, n, x) = (100, 1, 1, 0, 1)` violates the bound by a factor of ~50 (1/2 vs 1/99). The root cause is the Runge phenomenon: real-analyticity + real sup bound is too weak to control complex Cauchy coefficient bounds.
- **The corrected statement requires complex-disk hypothesis**: replace `AnalyticOn ℝ f (Ioo (a-R) (a+R))` + `∀ y ∈ Ioo, |f y| ≤ M` with `HasFPowerSeriesOnBall f p a (ENNReal.ofReal R)` + `∀ z ∈ Metric.ball a R, ‖f z‖ ≤ M`. Also fix the RHS: `M·r^(n+1)/(R^n·(R-r))` instead of `M·r^(n+1)/(R-r)`. The explicit `R^n` factor in the denominator is essential.
- **Mathlib's `AnalyticOn.div` recipe is clean**: For rational functions on intervals avoiding the real zeros of the denominator, `analyticOn_id ℝ` + `.pow` + `analyticOn_const` + `.add` + `.div` with `positivity` discharging the nonzero hypothesis is a 6-line proof.
- **Grandparent file `MeanValueTheoremOQ02.lean` had Mathlib drift**: the deprecated `∑ k in Finset.range` syntax broke the build; one-character fix to `∑ k ∈` and removal of a redundant `ring` (post-simp goal closure) unblocked downstream.

### Files Modified

- **New**: `proofs/Proofs/MeanValueTheoremOQ02OQ04OQ01.lean` (280 lines, 0 axioms, 1 sorry)
- **New**: `src/data/proofs/mean-value-theorem-oq-02-oq-04-oq-01/{meta.json, index.ts, annotations.json}`
- **New**: `src/data/research/problems/mean-value-theorem-oq-02-oq-04-oq-01.json`
- **New**: `research/problems/mean-value-theorem-oq-02-oq-04-oq-01/{knowledge.md, state.md}`
- **Modified**: `proofs/Proofs/MeanValueTheoremOQ02.lean` — Mathlib drift fix: `∑ k in` → `∑ k ∈` (line 56); removed redundant `ring` after simp closure (line 69)

### Next Steps

- **S2**: Discharge `analytic_taylor_remainder_uniform_bound_complex` via the documented Mathlib chain (`HasFPowerSeriesOnBall.uniform_geometric_approx'` + `FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius` + geometric tail summation). Estimated proof length: 100-200 lines.
- **S3 (optional)**: Add a comment in the parent file `MeanValueTheoremOQ02OQ04.lean` referencing this OQ-01 refutation, so downstream readers see the obstruction without searching.
- **Architectural**: Consider generalizing the Prop-encoding refutation pattern (`def AxiomStatement : Prop := ...; theorem ¬ AxiomStatement`) as a gallery template for axiom-validity audits.
