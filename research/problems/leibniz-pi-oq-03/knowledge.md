# Knowledge Base: leibniz-pi-oq-03

Leibniz Series Acceleration via Euler/Richardson Transforms

---

## Problem Understanding

The Leibniz series π/4 = Σ (-1)^n/(2n+1) converges at rate O(1/N).
This OQ formalizes two acceleration methods:
1. **Midpoint acceleration**: M(k) = (S(2k)+S(2k+1))/2 achieves error ≤ 1/(2(4k+1))
2. **Euler transform**: π/4 = Σ (1/2)^{n+1} ∫₀¹(1-t²)^n dt (geometric convergence)

---

## Session 2026-04-05 (Session 2) — Eliminate Last Sorry

**Mode**: REVISIT
**Outcome**: completed (0 sorries)

### What I Did

- Identified root cause of hidden sorry warning: `Summable.tsum_ofReal_ne_top` is not a Mathlib lemma
- Replaced with `ENNReal.ofReal_tsum_of_nonneg hnn hsum` + `ENNReal.ofReal_lt_top`
- Built `hf_bound` using `MeasureTheory.lintegral_const`, `Measure.restrict_apply_univ`, `Real.volume_Ioc`
- Verified 0 sorry warnings via docker build
- Committed and pushed to PR #9857

### Key Findings

- `Summable.tsum_ofReal_ne_top` does NOT exist in Mathlib v4.26 — it was the source of the hidden sorry
- Correct approach: `rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]; exact ENNReal.ofReal_lt_top`
- `enorm_of_nonneg` + `ENNReal.ofReal_le_ofReal` + `mul_le_of_le_one_right` handles the per-term bound

### Files Modified

- `proofs/Proofs/LeibnizPiOQ03.lean` (275 lines, 0 sorries)

---

## Session 2026-04-04 (Session 1) — Near-Complete Proof

**Mode**: FRESH
**Outcome**: progress (1 sorry remaining)

### What I Did

- Claimed problem, created `proofs/Proofs/LeibnizPiOQ03.lean`
- Part I: Proved midpoint acceleration with `midpoint_error_bound` and `midpoint_vs_raw` (0 sorries)
- Part II: Proved all Euler transform infrastructure (0 sorries); 1 sorry remains for sum-integral exchange in `euler_transform_eq`

### Key Findings

- `inv_div : (a/b)⁻¹ = b/a` is the key lemma for `geometric_series_eq` — avoids `field_simp` case splits
- `field_simp` on field equalities involving `⁻¹` creates case splits that `ring` can't close; use `inv_div` + `ring` instead
- `field_simp` alone (no `ring`) closes `1/(4k+1)/2 = 1/(2*(4k+1))` when denominators are provably nonzero
- `intervalIntegral.integral_mono_on` (not `integral_le_integral_of_nonneg_of_le_nonneg_left` which doesn't exist) is the right API for `∫ f ≤ ∫ g` on intervals
- `Summable.congr` + `mul_comm` + `← pow_succ` gives `Summable (fun n => (1/2)^(n+1))` from `summable_geometric.mul_left`
- `midpoint_error_bound` key rewrite: `(S(2k)+S(2k+1))/2 - π/4 = (S(2k+1)-S(2k))/2 - (π/4-S(2k))` then `rw [hgap, abs_le]; constructor <;> linarith`
- `gap_eq`: `convert h using 2; push_cast; ring` to unify `1/(4k+1)` with `1/(2*(2k)+1)`

### The 1 Remaining Sorry

`euler_transform_eq` needs: `∑' n, (1/2)^{n+1} * ∫₀¹(1-t²)^n dt = π/4`

This requires swapping `∑'` and `∫`, justified by dominated convergence: each `(1/2)^{n+1}(1-t²)^n ≤ (1/2)^{n+1}` uniformly, and `∑ (1/2)^{n+1} < ∞`. The relevant Mathlib lemma is `MeasureTheory.integral_tsum` but getting the measurability and integrability conditions right needs more investigation.

Aristotle classification: **HARD** (known mathematical result, needs Mathlib formalization)

### Files Modified

- `proofs/Proofs/LeibnizPiOQ03.lean` (new, 228 lines)

### Next Steps

- Submit `euler_transform_eq` sorry to Aristotle
- If Aristotle succeeds: proof is complete (0 sorries)
- If not: investigate `MeasureTheory.integral_tsum` conditions manually

---

## Insights

1. `inv_div` avoids `field_simp` case splits for inverses of quotients: `((a/b)⁻¹ = b/a)`
2. `intervalIntegral.integral_mono_on` requires `IntervalIntegrable` for both functions + pointwise bound
3. `simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, sub_zero]` simplifies `∫ 1 = 1` on `[0,1]`
4. The geometric series identity uses `hasSum_geometric_of_lt_one` with `(1-t²)/2` as ratio

---

## Dead Ends

- `intervalIntegral.integral_le_integral_of_nonneg_of_le_nonneg_left` — does not exist in Mathlib4
- `summable_of_norm_bounded` — not found; use `Summable.of_nonneg_of_le` instead
- `simp_rw [← pow_succ] at this` — "simp made no progress"; use `Summable.congr` instead
- `field_simp; ring` for `1/(1+t^2) = (1/2)*(1-(1-t^2)/2)⁻¹` — `field_simp` creates case splits, `ring` fails; fix with `rw [inv_div]; ring`
