# shannon-entropy-oq-01
## Differential Entropy Formalization — Proved gaussian_max_entropy via Gibbs inequality

**Status: IN PROGRESS** — 4 theorems fully proved. 2 sorries remain (scale equivariance, gaussian entropy value).

---

## Summary

`ShannonEntropyOQ01.lean` (330 lines) formalizes differential entropy for continuous distributions:
- `differentialEntropy f = -∫ x, f x * log (f x)`
- KL divergence non-negativity (Gibbs inequality)
- Translation invariance
- Gaussian maximizes entropy at fixed variance

**Proved (0 sorries)**:
- `kl_divergence_continuous_nonneg`: D(f||g) ≥ 0 for probability densities
- `gibbs_inequality_continuous`: h(f) ≤ -∫ f log g (Gibbs corollary)
- `differentialEntropy_translation_invariant`: h(f(·-c)) = h(f)
- `gaussian_max_entropy`: for densities with ∫x²f ≤ σ², h(f) ≤ ½log(2πeσ²)

**Still sorry**:
- `differentialEntropy_scale_equivariant`: h(f(·/a)/|a|) = h(f) + log|a| — needs measure-theoretic substitution
- `gaussianDifferentialEntropy`: h(gaussianPDF μ σ) = ½log(2πeσ²) — needs Gaussian second moment

---

## Session Log

### Session 2026-04-03 (Session 1)
**Mode**: FRESH
**Outcome**: progress

**What Was Done**:
1. Created `ShannonEntropyOQ01.lean` from scratch (330 lines)
2. Proved `kl_divergence_continuous_nonneg` via pointwise bound `p*log(p/q) ≥ p - q`
3. Proved `gibbs_inequality_continuous` using KL + integral_sub
4. Proved `differentialEntropy_translation_invariant` via Lebesgue translation invariance
5. Proved `gaussian_max_entropy` via Gibbs + Gaussian log expansion:
   - log(gaussianPDF 0 σ x) = -½log(2πσ²) - x²/(2σ²)
   - Integrate: -∫f log g = ½log(2πσ²) + (1/(2σ²))·∫x²f ≤ ½log(2πeσ²)
   - Variance bound: (1/(2σ²))·σ² ≤ ½

**Key Lean Fixes**:
1. `∫x, A - ∫x, B` parses as `∫x, (A - ∫x, B)` — MUST write `(∫x, A) - ∫x, B`
2. `congr 1; ring` doesn't peel off `exp`; need `congr 1; congr 1; ring` (two layers: `HMul` then `exp`)
3. `inv_ne_zero.mpr` unknown — use `(inv_pos.mpr (Real.sqrt_pos_of_pos (by positivity))).ne'`
4. `fun_prop` can't prove measurability of custom `gaussianPDF`; use `hrw : gaussianPDF = fun x => ...` + `rw [hrw]` + `integrable_exp_neg_mul_sq`
5. `simp only [sub_zero]` may fail in `hg_sum`; use explicit `hrw : gaussianPDF 0 σ x = ... := by congr 1; congr 1; ring`
6. `field_simp; ring` where `field_simp` already closes the goal → remove `ring`

**Files Modified**:
- `proofs/Proofs/ShannonEntropyOQ01.lean` (new file, 330 lines)
- `src/data/research/problems/shannon-entropy-oq-01.json`

**Next Steps**:
1. `gaussianDifferentialEntropy`: look for `MeasureTheory.integral_mul_exp_neg_mul_sq` or prove ∫x, x²·exp(-bx²) = √π/(2b^(3/2)) locally (50 lines estimate)
2. `differentialEntropy_scale_equivariant`: use `integral_comp_mul_right` or change of variables theorem in Mathlib (`MeasureTheory.integral_comp_mul_right` or `lintegral_comp_mul_right`)

---

## Key Mathematical Insights

1. **gaussian_max_entropy proof via Gibbs**: The core is that for any density g,
   h(f) ≤ -∫f log g. Taking g = gaussianPDF 0 σ and expanding:
   log(gaussianPDF 0 σ x) = -½log(2πσ²) - x²/(2σ²)
   gives -∫f log g = ½log(2πσ²) + (1/(2σ²))·E[X²] ≤ ½log(2πσ²) + ½ = ½log(2πeσ²).

2. **Lean 4 integral subtraction parsing trap**: `∫x, A - ∫x, B` is NOT `(∫x, A) - (∫x, B)`.
   The integral binder consumes everything to its right. Always use explicit parentheses.

3. **gaussianPDF integrability route**: Use `integrable_exp_neg_mul_sq (h : 0 < b)`
   after rewriting `gaussianPDF 0 σ x = C * exp(-b*x²)` with `b = 1/(2σ²)`.
   The `fun_prop` approach fails for custom definitions.
