# shannon-entropy-oq-01
## Differential Entropy Formalization — COMPLETE

**Status: COMPLETED** — All sorries eliminated. Build succeeds with 0 errors.

---

## Summary

`ShannonEntropyOQ01.lean` (~475 lines) formalizes differential entropy for continuous distributions:
- `differentialEntropy f = -∫ x, f x * log (f x)`
- KL divergence non-negativity (Gibbs inequality)
- Translation invariance, scale equivariance
- Gaussian maximizes entropy at fixed variance
- Gaussian entropy formula: h(N(μ,σ²)) = ½log(2πeσ²) — **fully proved**

**All theorems proved (0 sorries)**:
- `kl_divergence_continuous_nonneg`: D(f||g) ≥ 0 for probability densities
- `gibbs_inequality_continuous`: h(f) ≤ -∫ f log g (Gibbs corollary)
- `differentialEntropy_translation_invariant`: h(f(·-c)) = h(f)
- `gaussian_max_entropy`: for densities with ∫x²f ≤ σ², h(f) ≤ ½log(2πeσ²)
- `differentialEntropy_scale_equivariant`: h((1/|a|)·f(·/a)) = h(f) + log|a|
- `gaussianDifferentialEntropy`: h(gaussianPDF μ σ) = ½log(2πeσ²)
- `gaussian_second_moment`: ∫ (x-μ)² · φ(x) dx = σ² — proved via IBP
- `gaussian_quad_integrable`: Integrable (fun x => (x-μ)² · φ(x)) — proved

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

### Session 2026-04-03 (Session 4) — COMPLETION
**Mode**: REVISIT
**Outcome**: completed

**What Was Done**:
1. Proved `gaussian_second_moment`: ∫(x-μ)²·φ(x)dx = σ² entirely in Lean without Aristotle
   - Used IBP with antiderivative G(x) = -x/(2b)·exp(-b·x²)
   - G'(x) = x²·exp(-bx²) - (1/2b)·exp(-bx²)
   - `integral_Ioi_of_hasDerivAt_of_tendsto'` + `integral_Iic_of_hasDerivAt_of_tendsto'` give ∫G'=0
   - ∫x²·exp(-bx²) = (1/2b)·∫exp(-bx²) = (1/2b)·√(π/b)
   - Translation invariance + algebra gives σ²
2. Proved `gaussian_quad_integrable` via `integrable_rpow_mul_exp_neg_mul_sq hb (s:=2)` + `comp_sub_right` + `const_mul`
3. Fixed `gaussianPDF_integrable`: `simp_rw` can't rewrite inside `Integrable(f)` (function, not pointwise). Fixed with `funext + rw`.
4. Fixed `mul_exp_tendsto_zero`: avoided `tendsto_pow_atTop` (unknown), `div_le_iff` (unknown), `pow_le_pow_left` (unknown). Used elementary squeeze via `mul_le_mul` + sqrt bounds.
5. Fixed alpha-equivalence issue: `(integral_sub h1 h2).symm.trans h_full_zero` fails (Eq.trans sees `∫(a:ℝ)` vs `∫(x:ℝ)`). Fix: `rw [integral_sub h1 h2] at h_full_zero` mutates the hypothesis instead.
6. Zero sorries. Build succeeds.

**Key Lean Findings**:
- `pow_le_pow_left` unavailable by that name — use `mul_le_mul` + `Real.sq_sqrt` + `nlinarith`
- `div_le_iff` may fail in `rw` — compute manually: `calc 2*(-M) = 2*(-M)/b * b := by field_simp [hb.ne']; _ ≤ x^2*b := mul_le_mul_of_nonneg_right hMx hb.le`
- `squeeze_zero` after `apply`: goals may be type-mismatched — use `tendsto_of_tendsto_of_tendsto_of_le_of_le'` directly
- Alpha-equiv: `Eq.trans` distinguishes `∫(a:ℝ), f a` from `∫(x:ℝ), f x` syntactically; `rw [...] at h` is the workaround
- `simp only [Filter.tendsto_atBot, Filter.eventually_atTop]` more robust than `rw [Filter.tendsto_atBot]`
- `linarith [...]` in term mode is invalid — must use `by linarith [...]`

**Files Modified**:
- `proofs/Proofs/ShannonEntropyOQ01.lean` (~330 → 475 lines; 0 sorries)
- `src/data/research/problems/shannon-entropy-oq-01.json`
- `research/problems/shannon-entropy-oq-01/knowledge.md`

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
