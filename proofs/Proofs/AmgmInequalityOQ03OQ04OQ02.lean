/-
# Tsallis Entropy: the q-deformed analogue of the AM-GM / Rényi entropy identity

## Open Question: amgm-inequality-oq-03-oq-04-oq-02

The parent entry `amgm-inequality-oq-03-oq-04` ("Rényi Entropy and Power Mean
Monotonicity") shows that the Rényi entropy

  H_α(p) = (1/(1-α)) · log(Σ pᵢ^α)

is the logarithm of a power mean:  H_α(p) = -log(M_{α-1}(p,p)).

This file establishes the **Tsallis-entropy analogue** of that identity. Tsallis
entropy replaces the ordinary logarithm by the **q-deformed logarithm**

  ln_q(x) = (x^{1-q} - 1) / (1 - q),

which satisfies ln_q(x) → log(x) as q → 1.  The Tsallis entropy is

  S_q(p) = (1 - Σ pᵢ^q) / (q - 1).

## What This File Proves

1. `qLog`, `tsallisEntropy` : the q-logarithm and Tsallis entropy.
2. `qLog_one`               : ln_q(1) = 0.
3. `qLog_mul`               : the **q-deformed (pseudo-additive) law of the
                              logarithm** ln_q(xy) = ln_q(x)+ln_q(y)+(1-q)·ln_q(x)·ln_q(y).
                              (As q→1 the cross term vanishes and this becomes log(xy)=log x+log y.)
4. `tsallis_eq_neg_sum_qLog`: S_q(p) = -Σ pᵢ^q · ln_q(pᵢ), the "escort" definition,
                              the exact q-analogue of Shannon's H = -Σ pᵢ log pᵢ.
5. `tsallis_eq_qLog_exp_renyi` : the **bridge to Rényi**, S_q(p) = ln_q(exp(H_q(p))),
                              the direct analogue of the parent's H_α = -log(M_{α-1}).
6. `tsallis_pseudo_additive`: the signature **non-extensivity** of Tsallis entropy
                              on a product distribution:
                              S_q(p⊗r) = S_q(p) + S_q(r) + (1-q)·S_q(p)·S_q(r).
7. `qLog_tendsto_log`       : the **q→1 limit** ln_q(x) → log(x) (x>0), the analytic
                              statement that recovers the Shannon case.

## References

- Tsallis, C. (1988). Possible generalization of Boltzmann-Gibbs statistics.
  J. Stat. Phys. 52, 479-487.
- Rényi, A. (1961). On measures of entropy and information. 4th Berkeley Symp.
-/

import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

open Filter Topology

namespace TsallisEntropy

variable {ι : Type*} (s : Finset ι) (p : ι → ℝ)

/-- The **Rényi entropy** of order α, H_α(p) = (1/(1-α)) · log(Σ pᵢ^α), reproduced
    here (matching the definition in the parent entry `amgm-inequality-oq-03-oq-04`)
    so that this file is self-contained. -/
noncomputable def renyiEntropy (α : ℝ) : ℝ :=
  (1 / (1 - α)) * Real.log (∑ i ∈ s, p i ^ α)

-- ============================================================
-- PART I: Definitions
-- ============================================================

/-- The **q-deformed logarithm** ln_q(x) = (x^{1-q} - 1)/(1-q).
    As q → 1 this converges to `Real.log x` (see `qLog_tendsto_log`). -/
noncomputable def qLog (q x : ℝ) : ℝ := (x ^ (1 - q) - 1) / (1 - q)

/-- The **Tsallis entropy** of order q for a distribution p on finset s:
    S_q(p) = (1 - Σ_{i∈s} pᵢ^q) / (q - 1).

    As q → 1 this converges to the Shannon entropy -Σ pᵢ log pᵢ. -/
noncomputable def tsallisEntropy (q : ℝ) : ℝ :=
  (1 - ∑ i ∈ s, p i ^ q) / (q - 1)

-- ============================================================
-- PART II: Algebra of the q-logarithm
-- ============================================================

/-- **ln_q(1) = 0**. -/
@[simp] theorem qLog_one (q : ℝ) : qLog q 1 = 0 := by
  unfold qLog; rw [Real.one_rpow]; simp

/-- **q-deformed law of the logarithm** (pseudo-additivity):
    ln_q(xy) = ln_q(x) + ln_q(y) + (1-q)·ln_q(x)·ln_q(y).

    The cross term `(1-q)·ln_q(x)·ln_q(y)` is the q-deformation; it vanishes as
    q→1, recovering the ordinary log(xy) = log x + log y. -/
theorem qLog_mul (q : ℝ) (hq : q ≠ 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    qLog q (x * y) = qLog q x + qLog q y + (1 - q) * qLog q x * qLog q y := by
  have hs : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr fun h => hq h.symm
  unfold qLog
  rw [Real.mul_rpow hx.le hy.le]
  field_simp
  ring

-- ============================================================
-- PART III: Escort ("-Σ p^q ln_q p") form of the entropy
-- ============================================================

/-- Pointwise: pᵢ^q · ln_q(pᵢ) = (pᵢ - pᵢ^q)/(1-q) for pᵢ > 0. -/
private lemma pow_mul_qLog (q : ℝ) {x : ℝ} (hx : 0 < x) :
    x ^ q * qLog q x = (x - x ^ q) / (1 - q) := by
  have hmul : x ^ q * x ^ (1 - q) = x := by
    rw [← Real.rpow_add hx]; norm_num
  unfold qLog
  rw [mul_div_assoc', mul_sub, mul_one, hmul]

/-- **Escort form of Tsallis entropy**: S_q(p) = -Σ pᵢ^q · ln_q(pᵢ).

    This is the exact q-analogue of the Shannon entropy H = -Σ pᵢ log pᵢ:
    it replaces `log` by the q-logarithm and re-weights by the escort powers pᵢ^q. -/
theorem tsallis_eq_neg_sum_qLog (q : ℝ) (hq : q ≠ 1)
    (hp : ∀ i ∈ s, 0 < p i) (hsum : ∑ i ∈ s, p i = 1) :
    tsallisEntropy s p q = - ∑ i ∈ s, p i ^ q * qLog q (p i) := by
  have hs : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr fun h => hq h.symm
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  have hstep : ∑ i ∈ s, p i ^ q * qLog q (p i)
      = (∑ i ∈ s, (p i - p i ^ q)) / (1 - q) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i hi => pow_mul_qLog q (hp i hi)
  rw [hstep, Finset.sum_sub_distrib, hsum, tsallisEntropy]
  field_simp
  ring

-- ============================================================
-- PART IV: Bridge to Rényi entropy
-- ============================================================

/-- **Bridge identity**: S_q(p) = ln_q(exp(H_q(p))), where H_q is the Rényi entropy
    of order q (from the parent entry `amgm-inequality-oq-03-oq-04`).

    This is the direct Tsallis analogue of the parent's power-mean identity
    H_α = -log(M_{α-1}(p,p)): the Tsallis entropy is obtained from the Rényi entropy
    by applying the q-exponential/q-logarithm pair instead of exp/log. -/
theorem tsallis_eq_qLog_exp_renyi (q : ℝ) (hq : q ≠ 1)
    (hp : ∀ i ∈ s, 0 < p i) (hs' : s.Nonempty) :
    tsallisEntropy s p q
      = qLog q (Real.exp (renyiEntropy s p q)) := by
  have hs : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr fun h => hq h.symm
  have hW : 0 < ∑ i ∈ s, p i ^ q :=
    Finset.sum_pos (fun i hi => Real.rpow_pos_of_pos (hp i hi) q) hs'
  unfold qLog tsallisEntropy renyiEntropy
  -- exp(H)^(1-q) = exp((1-q)·H); simplify the exponent to log(Σ pᵢ^q)
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hexp : 1 / (1 - q) * Real.log (∑ i ∈ s, p i ^ q) * (1 - q)
      = Real.log (∑ i ∈ s, p i ^ q) := by field_simp
  rw [hexp, Real.exp_log hW]
  rw [div_eq_div_iff (sub_ne_zero.mpr hq) hs]
  ring

-- ============================================================
-- PART V: Non-extensivity (pseudo-additivity of the entropy)
-- ============================================================

/-- **Non-extensivity of Tsallis entropy**: for a product (independent) distribution
    `(i,j) ↦ pᵢ · rⱼ` on `s ×ˢ t`,

      S_q(p⊗r) = S_q(p) + S_q(r) + (1-q)·S_q(p)·S_q(r).

    The cross term `(1-q)·S_q(p)·S_q(r)` is the signature departure from the ordinary
    additivity of Shannon entropy; it vanishes as q→1. -/
theorem tsallis_pseudo_additive (q : ℝ) (hq : q ≠ 1)
    {κ : Type*} (t : Finset κ) (r : κ → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) (hr : ∀ j ∈ t, 0 < r j) :
    tsallisEntropy (s ×ˢ t) (fun ij => p ij.1 * r ij.2) q
      = tsallisEntropy s p q + tsallisEntropy t r q
        + (1 - q) * tsallisEntropy s p q * tsallisEntropy t r q := by
  have hq1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  -- the escort sum of the product factorizes
  have hfactor : ∑ ij ∈ s ×ˢ t, (p ij.1 * r ij.2) ^ q
      = (∑ i ∈ s, p i ^ q) * (∑ j ∈ t, r j ^ q) := by
    rw [Finset.sum_product, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    exact Real.mul_rpow (hp i hi).le (hr j hj).le
  unfold tsallisEntropy
  rw [hfactor]
  field_simp
  ring

-- ============================================================
-- PART VI: The q → 1 limit (recovering the Shannon logarithm)
-- ============================================================

/-- **The q → 1 limit**: ln_q(x) → log(x) for x > 0.

    This is the analytic statement that the Tsallis / q-deformed framework degenerates
    to the ordinary (Shannon) case as q → 1.  It is the derivative of `u ↦ x^u` at
    `u = 0`, whose value is `log x`, read off as a slope limit. -/
theorem qLog_tendsto_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun q => qLog q x) (𝓝[≠] 1) (𝓝 (Real.log x)) := by
  -- Work with G u = (exp(log x · u) - 1)/u, the slope of u ↦ exp(log x · u) at 0.
  set c := Real.log x with hc
  -- HasDerivAt of u ↦ exp(c·u) at 0 is c.
  have hlin : HasDerivAt (fun u : ℝ => c * u) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul c
  have hderiv : HasDerivAt (fun u : ℝ => Real.exp (c * u)) c 0 := by
    have h := (Real.hasDerivAt_exp (c * 0)).comp 0 hlin
    simpa using h
  have hslope := hasDerivAt_iff_tendsto_slope.mp hderiv
  -- Rewrite the slope function explicitly.
  have hG : Tendsto (fun u : ℝ => (Real.exp (c * u) - 1) / u) (𝓝[≠] 0) (𝓝 c) := by
    refine hslope.congr fun u => ?_
    rw [slope_def_field]
    simp [mul_zero, Real.exp_zero, sub_zero]
  -- Reparametrize q ↦ 1 - q : 𝓝[≠] 1 → 𝓝[≠] 0.
  have hφ : Tendsto (fun q : ℝ => 1 - q) (𝓝[≠] 1) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h1 : Tendsto (fun q : ℝ => 1 - q) (𝓝 (1 : ℝ)) (𝓝 0) := by
        have h : Tendsto (fun q : ℝ => 1 - q) (𝓝 (1 : ℝ)) (𝓝 (1 - 1)) :=
          Filter.Tendsto.const_sub 1 tendsto_id
        simpa using h
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hq ⊢
      intro h; exact hq (by linarith)
  have hcomp := hG.comp hφ
  -- G(1-q) = ln_q(x).
  refine hcomp.congr fun q => ?_
  show (Real.exp (c * (1 - q)) - 1) / (1 - q) = qLog q x
  unfold qLog
  rw [hc, ← Real.rpow_def_of_pos hx]

end TsallisEntropy
