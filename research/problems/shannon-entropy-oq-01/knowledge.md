# shannon-entropy-oq-01
## Differential Entropy Formalization — Near complete: 2 moment lemmas pending Aristotle

**Status: IN PROGRESS** — All top-level theorems proved. 2 helper sorries remain (Gaussian moment lemmas, queued for Aristotle when pipeline unblocks).

---

## Summary

`ShannonEntropyOQ01.lean` (~400 lines) formalizes differential entropy for continuous distributions:
- `differentialEntropy f = -∫ x, f x * log (f x)`
- KL divergence non-negativity (Gibbs inequality)
- Translation invariance, scale equivariance
- Gaussian maximizes entropy at fixed variance
- Gaussian entropy formula: h(N(μ,σ²)) = ½log(2πeσ²)

**Proved (0 sorries in body)**:
- `kl_divergence_continuous_nonneg`: D(f||g) ≥ 0 for probability densities
- `gibbs_inequality_continuous`: h(f) ≤ -∫ f log g (Gibbs corollary)
- `differentialEntropy_translation_invariant`: h(f(·-c)) = h(f)
- `gaussian_max_entropy`: for densities with ∫x²f ≤ σ², h(f) ≤ ½log(2πeσ²)
- `differentialEntropy_scale_equivariant`: h((1/|a|)·f(·/a)) = h(f) + log|a| [Session 2]
- `gaussianDifferentialEntropy`: h(gaussianPDF μ σ) = ½log(2πeσ²) modulo moment lemmas [Session 2]

**Pending (Aristotle)**:
- `gaussian_second_moment`: ∫ (x-μ)² · φ(x) dx = σ² — submitted to Aristotle
- `gaussian_quad_integrable`: Integrable (fun x => (x-μ)² · φ(x)) — submitted to Aristotle

**PR**: #8914

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

### Session 2026-04-03 (Session 2)
**Mode**: REVISIT
**Outcome**: progress

**What Was Done**:
1. Proved `differentialEntropy_scale_equivariant` (previously sorry):
   - Key: `MeasureTheory.Measure.integral_comp_div (g := f) a` gives `∫f(x/a) = |a|•∫f`
   - `simp only [smul_eq_mul]` converts SMul to multiplication
   - `Integrable.comp_div ha` handles integrability under scaling
   - Pointwise: `log((1/|a|)·f(x/a)) = -log|a| + log(f(x/a))` via `Real.log_mul` + `Real.log_inv`
   - Added hypotheses: `hf_nn`, `hf_int`, `hflog_int` (previously missing)
2. Proved `gaussianDifferentialEntropy` modulo two moment lemmas:
   - Helper lemmas via `ProbabilityTheory.gaussianPDFReal`: normalization, integrability, log expansion
   - `gaussianPDF_log`: expands log density as `-½log(2πσ²) - (x-μ)²/(2σ²)`
   - Integrates two-term sum: constant × normalization + constant × second moment
   - Two remaining sorries submitted to Aristotle companion file
3. Created `ShannonEntropyOQ01Aristotle.lean` with `gaussian_second_moment` and `gaussian_quad_integrable`
4. PR #8914 created

**Key Lean Findings**:
- `MeasureTheory.Measure.integral_comp_div` is in `Mathlib.MeasureTheory.Measure.Haar.NormedSpace`
- `ProbabilityTheory.gaussianPDFReal μ ⟨σ², sq_nonneg σ⟩` bridges to our `gaussianPDF μ σ` via `NNReal.coe_mk`
- `ProbabilityTheory.integral_gaussianPDFReal_eq_one` needs `NNReal.ne_iff` to prove variance ≠ 0
- `pow_pos hσ 2` gives `0 < σ^2` (not `sq_pos_of_pos`)

**Files Modified**:
- `proofs/Proofs/ShannonEntropyOQ01.lean` (330 → ~400 lines; both top-level sorries proved)
- `proofs/Proofs/ShannonEntropyOQ01Aristotle.lean` (new, Aristotle targets)
- `src/data/research/problems/shannon-entropy-oq-01.json`

**Next Steps**:
1. Check Aristotle results for `gaussian_second_moment` and `gaussian_quad_integrable`
2. Integrate solutions → zero sorries in main file
3. Update status to `completed`

### Session 2026-04-03 (Session 3)
**Mode**: REVISIT
**Outcome**: build fix

**What Was Done**:
1. Fixed `gaussianPDF_integrable`: `simp_rw` can't rewrite inside `Integrable(f)` (function, not pointwise). Fixed with `funext + rw`.
2. Build now passes: `docker-build.sh Proofs.ShannonEntropyOQ01` succeeds (2 sorry warnings only).
3. PR #8914 already merged to main.
4. Aristotle pipeline blocked by 11 orphaned server jobs (Mechanic issue).
   `ShannonEntropyOQ01Aristotle.lean` is queued as Tier 1 candidate for when pipeline unblocks.

**Key Lean Finding**:
- `simp_rw [h]` where `h : ∀ x, f x = g x` fails for `Integrable (f)` — no explicit `x` application for simp to match.
- Fix: `have heq : f = g := funext h; rw [heq]`

**Files Modified**:
- `proofs/Proofs/ShannonEntropyOQ01.lean` (line 274: gaussianPDF_integrable fix)

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
