/-
  Power Mean Limit: lim_{r→0} M_r = GM (Geometric Mean)
  Open Question: amgm-inequality-oq-03-oq-02

  The weighted power mean M_r(z, w) = (∑ wᵢ zᵢ^r)^(1/r) has a well-known
  singularity at r = 0. The classical theorem states that the limit equals
  the weighted geometric mean:

    lim_{r→0} M_r(z, w) = ∏ zᵢ^wᵢ = GM(z, w)

  This is the continuous extension that makes the power mean chain
  HM = M_{-1} ≤ M_0 = GM ≤ M_1 = AM ≤ M_2 ≤ ... complete.

  Proof approach (via exp/log):
    M_r = exp((1/r) · log(∑ wᵢ zᵢ^r))
    Let f(r) = log(∑ wᵢ zᵢ^r); then f(0) = log(1) = 0
    f'(0) = (∑ wᵢ zᵢ^0 · log zᵢ) / (∑ wᵢ) = ∑ wᵢ log zᵢ  (chain rule + diff under sum)
    So f(r)/r → f'(0) = ∑ wᵢ log zᵢ  (definition of derivative)
    Then M_r = exp(f(r)/r) → exp(∑ wᵢ log zᵢ) = ∏ zᵢ^wᵢ = GM  (continuity of exp)

  Mathlib Status:
  - HasDerivAt for exp, log, rpow: available
  - Differentiating finite sums term-by-term: HasDerivAt.sum
  - Derivative of a^x w.r.t. x: Real.hasStrictDerivAt_const_rpow
  - Slope/derivative equivalence: hasDerivAt_iff_tendsto_slope
  - Continuity of exp: available

  References:
  - Hardy, Littlewood, Pólya "Inequalities" (1934), §2.9
  - Wikipedia: Power mean, "Generalized mean"
  - Mathlib.Analysis.SpecialFunctions.Pow.Real
  - Mathlib.Analysis.SpecialFunctions.Log.Deriv
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

open Finset Real Filter

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-
## Auxiliary: Sum Positivity
-/

/-- When weights are non-negative with sum 1, and all zᵢ > 0, the weighted sum ∑ wᵢ zᵢ^r > 0. -/
private lemma sum_weighted_rpow_pos
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (r : ℝ) :
    0 < ∑ i ∈ s, w i * z i ^ r := by
  -- Since ∑ wᵢ = 1 and all wᵢ ≥ 0, some wᵢ > 0
  obtain ⟨i₀, hi₀, hwi₀⟩ : ∃ i ∈ s, 0 < w i := by
    by_contra h
    push_neg at h
    have hzero : ∀ i ∈ s, w i = 0 := fun i hi => le_antisymm (h i hi) (hw i hi)
    have := Finset.sum_eq_zero hzero
    linarith
  calc 0 < w i₀ * z i₀ ^ r :=
          mul_pos hwi₀ (Real.rpow_pos_of_pos (hz i₀ hi₀) r)
    _ ≤ ∑ i ∈ s, w i * z i ^ r :=
          Finset.single_le_sum
            (fun i hi => mul_nonneg (hw i hi) (le_of_lt (Real.rpow_pos_of_pos (hz i hi) r)))
            hi₀

/-
## Part I: The Derivative of ∑ wᵢ zᵢ^r at r = 0
-/

/-- For zᵢ > 0 and wᵢ ≥ 0, the function r ↦ ∑ wᵢ zᵢ^r has derivative
    ∑ wᵢ log(zᵢ) at r = 0.

    Proof: zᵢ^r = exp(r · log zᵢ), so d/dr[zᵢ^r]|_{r=0} = log(zᵢ).
    Differentiate the finite sum term-by-term. -/
theorem hasDerivAt_sum_weighted_rpow_zero
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    HasDerivAt (fun (r : ℝ) => ∑ i ∈ s, w i * z i ^ r)
               (∑ i ∈ s, w i * Real.log (z i)) 0 := by
  refine HasDerivAt.sum (fun i hi => ?_)
  have hzi : (0 : ℝ) < z i := hz i hi
  -- d/dr[zᵢ^r]|_{r=0} = zᵢ^0 · log(zᵢ) = log(zᵢ)
  have hderiv : HasDerivAt (fun (r : ℝ) => z i ^ r) (Real.log (z i)) 0 := by
    have h := (Real.hasStrictDerivAt_const_rpow hzi 0).hasDerivAt
    simp only [Real.rpow_zero, one_mul] at h
    exact h
  -- d/dr[wᵢ · zᵢ^r]|_{r=0} = wᵢ · log(zᵢ)
  have hmul := hderiv.const_mul (w i)
  simp only [mul_comm (w i)] at hmul
  exact hmul

/-
## Part II: The Log Identity f(0) = 0
-/

/-- The function r ↦ log(∑ wᵢ zᵢ^r) has value 0 at r = 0 (when ∑ wᵢ = 1). -/
theorem log_sum_weighted_rpow_zero
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) :
    Real.log (∑ i ∈ s, w i * z i ^ (0 : ℝ)) = 0 := by
  simp only [Real.rpow_zero, mul_one]
  rw [hw', Real.log_one]

/-
## Part III: HasDerivAt for log(∑ wᵢ zᵢ^r) at r = 0
-/

/-- The function r ↦ log(∑ wᵢ zᵢ^r) has derivative ∑ wᵢ log(zᵢ) at r = 0.

    Chain rule: (log ∘ h)'(0) = h'(0) / h(0) = (∑ wᵢ log zᵢ) / 1 = ∑ wᵢ log zᵢ. -/
private lemma hasDerivAt_log_sum_weighted_rpow
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) :
    HasDerivAt (fun (r : ℝ) => Real.log (∑ i ∈ s, w i * z i ^ r))
               (∑ i ∈ s, w i * Real.log (z i)) 0 := by
  -- h(0) = 1 (since ∑ wᵢ = 1 and zᵢ^0 = 1)
  have hh_zero : ∑ i ∈ s, w i * z i ^ (0 : ℝ) = 1 := by
    simp only [Real.rpow_zero, mul_one]; exact hw'
  -- h(0) ≠ 0 (it's 1)
  have hh_ne : (∑ i ∈ s, w i * z i ^ (0 : ℝ)) ≠ 0 := by
    rw [hh_zero]; norm_num
  -- HasDerivAt for h = ∑ wᵢ zᵢ^r
  have hh := hasDerivAt_sum_weighted_rpow_zero s w z hz hw
  -- Apply chain rule via Real.hasDerivAt_log.comp: (log ∘ h)' = h'(0) / h(0)
  have hlog := (Real.hasDerivAt_log hh_ne).comp (0 : ℝ) hh
  simp only [hh_zero, inv_one, one_mul] at hlog
  exact hlog

/-
## Part IV: The Core Limit via Derivative Definition
-/

/-- KEY LEMMA: (log ∑ wᵢ zᵢ^r) / r → ∑ wᵢ log zᵢ as r → 0.

    This follows from the definition of derivative:
    f(r) / r = (f(r) - f(0)) / (r - 0) → f'(0) = ∑ wᵢ log zᵢ.

    We use `hasDerivAt_iff_tendsto_slope` which connects HasDerivAt
    to the limit of the difference quotient (slope). -/
theorem tendsto_log_sum_div_rpow
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) :
    Filter.Tendsto
      (fun r => Real.log (∑ i ∈ s, w i * z i ^ r) / r)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (∑ i ∈ s, w i * Real.log (z i))) := by
  -- g(0) = log(1) = 0
  have hg_zero : Real.log (∑ i ∈ s, w i * z i ^ (0 : ℝ)) = 0 :=
    log_sum_weighted_rpow_zero s w z hz hw hw'
  -- HasDerivAt g (∑ wᵢ log zᵢ) 0
  have hg_deriv : HasDerivAt (fun (r : ℝ) => Real.log (∑ i ∈ s, w i * z i ^ r))
      (∑ i ∈ s, w i * Real.log (z i)) 0 :=
    hasDerivAt_log_sum_weighted_rpow s w z hz hw hw'
  -- By hasDerivAt_iff_tendsto_slope: slope g 0 → ∑ wᵢ log zᵢ
  rw [hasDerivAt_iff_tendsto_slope] at hg_deriv
  -- slope g 0 r = (g r - g 0) / (r - 0) = g r / r  (since g 0 = 0)
  -- equality holds for all r (including r = 0 where both sides = 0)
  exact hg_deriv.congr (fun r => by
    simp only [slope, sub_zero, hg_zero, smul_eq_mul]
    ring)

/-
## Part V: Supporting Identities
-/

/-- The geometric mean can be written as exp(∑ wᵢ log zᵢ). -/
theorem geomMean_eq_exp_sum_log
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∏ i ∈ s, z i ^ w i = Real.exp (∑ i ∈ s, w i * Real.log (z i)) := by
  have hprod_pos : 0 < ∏ i ∈ s, z i ^ w i :=
    Finset.prod_pos (fun i hi => Real.rpow_pos_of_pos (hz i hi) (w i))
  rw [← Real.exp_log hprod_pos]
  congr 1
  rw [Real.log_prod (fun i hi => ne_of_gt (Real.rpow_pos_of_pos (hz i hi) (w i)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_rpow (hz i hi)]

/-- For r = 1, the power mean equals the arithmetic mean. -/
theorem powerMean_one_eq_arithMean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∑ i ∈ s, w i * z i ^ (1 : ℝ)) = ∑ i ∈ s, w i * z i := by
  simp [Real.rpow_one]

/-
## Part VI: The Algebraic Identity for Power Mean
-/

/-- For r ≠ 0 and all zᵢ > 0 with ∑ wᵢ = 1, the power mean equals
    exp((log(∑ wᵢ zᵢ^r)) / r). -/
theorem powerMean_eq_exp_log
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    {r : ℝ} (hr : r ≠ 0) :
    (∑ i ∈ s, w i * z i ^ r) ^ (1 / r) =
    Real.exp ((1 / r) * Real.log (∑ i ∈ s, w i * z i ^ r)) := by
  have hsum_pos : 0 < ∑ i ∈ s, w i * z i ^ r :=
    sum_weighted_rpow_pos s w z hz hw hw' r
  rw [Real.rpow_def_of_pos hsum_pos]
  congr 1; ring

/-
## Part VII: Main Limit Theorem
-/

/-- **The Power Mean Limit Theorem**: lim_{r→0} M_r(z, w) = GM(z, w).

    As r → 0, the weighted power mean converges to the weighted geometric mean.

    The standard proof chain:
    M_r = exp(f(r)/r) where f(r) = log(∑ wᵢ zᵢ^r)
    f(r)/r → ∑ wᵢ log zᵢ   (f(0) = 0, f'(0) = ∑ wᵢ log zᵢ)
    M_r → exp(∑ wᵢ log zᵢ) = ∏ zᵢ^wᵢ = GM(z, w) -/
theorem tendsto_powerMean_zero
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    Filter.Tendsto
      (fun r => (∑ i ∈ s, w i * z i ^ r) ^ (1 / r))
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (∏ i ∈ s, z i ^ w i)) := by
  -- Step 1: f(r)/r → ∑ wᵢ log zᵢ
  have hL := tendsto_log_sum_div_rpow s w z hz hw hw'
  -- Step 2: Rewrite GM target to exp form
  rw [geomMean_eq_exp_sum_log s w z hz hw]
  -- Step 3: Rewrite power mean to exp form under the binder
  have h_eq : ∀ r : ℝ, (∑ i ∈ s, w i * z i ^ r) ^ (1 / r : ℝ) =
      Real.exp (Real.log (∑ i ∈ s, w i * z i ^ r) / r) := fun r => by
    rw [Real.rpow_def_of_pos (sum_weighted_rpow_pos s w z hz hw hw' r)]
    congr 1; ring
  simp_rw [h_eq]
  -- Step 4: exp ∘ (f(r)/r) → exp(∑ wᵢ log zᵢ) by continuity of exp
  exact Real.continuous_exp.continuousAt.tendsto.comp hL

/-
## Part VIII: HM ≤ GM ≤ AM (Completing the Power Mean Chain)
-/

/-- The power mean M_0 (geometric mean as the limit) satisfies M_{-1} ≤ M_0 ≤ M_1.

    Specifically:
    - HM = M_{-1} = (∑ wᵢ/zᵢ)⁻¹ ≤ GM = M_0 = ∏ zᵢ^wᵢ  (via AM-GM on inverses)
    - GM = M_0 ≤ M_1 = AM = ∑ wᵢ zᵢ  (classical AM-GM from Mathlib) -/
theorem powerMean_neg1_le_geomMean_le_arithMean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i * (z i)⁻¹)⁻¹ ≤ ∏ i ∈ s, z i ^ w i ∧
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i := by
  constructor
  · -- HM ≤ GM: Apply AM-GM to z⁻¹, then invert
    -- GM(z⁻¹, w) = (GM(z,w))⁻¹ and GM(z⁻¹,w) ≤ AM(z⁻¹,w) = ∑ wᵢ/zᵢ
    have hz_nn : ∀ i ∈ s, 0 ≤ z i := fun i hi => le_of_lt (hz i hi)
    have hz_inv_nn : ∀ i ∈ s, 0 ≤ (z i)⁻¹ := fun i hi => inv_nonneg.mpr (hz_nn i hi)
    -- GM(z,w) > 0
    have hGM_pos : 0 < ∏ i ∈ s, z i ^ w i := by
      apply Finset.prod_pos
      intro i hi; exact Real.rpow_pos_of_pos (hz i hi) (w i)
    -- AM-GM applied to inverses: ∏ (zᵢ⁻¹)^wᵢ ≤ ∑ wᵢ · zᵢ⁻¹
    have amgm_inv : ∏ i ∈ s, (z i)⁻¹ ^ w i ≤ ∑ i ∈ s, w i * (z i)⁻¹ :=
      Real.geom_mean_le_arith_mean_weighted s w (fun i => (z i)⁻¹) hw hw' hz_inv_nn
    -- ∏ (zᵢ⁻¹)^wᵢ = (∏ zᵢ^wᵢ)⁻¹
    have hprod_inv : ∏ i ∈ s, (z i)⁻¹ ^ w i = (∏ i ∈ s, z i ^ w i)⁻¹ := by
      rw [← Finset.prod_inv_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      -- (z i)⁻¹ ^ w i = (z i ^ (-1))^(w i) = z i^(-w i) = (z i^(w i))⁻¹
      have hzi_nn : 0 ≤ z i := le_of_lt (hz i hi)
      have inv_eq : (z i)⁻¹ = z i ^ (-1 : ℝ) := by
        rw [eq_comm, Real.rpow_neg hzi_nn, Real.rpow_one]
      rw [inv_eq, ← Real.rpow_mul hzi_nn, neg_one_mul, Real.rpow_neg hzi_nn]
    rw [hprod_inv] at amgm_inv
    -- (GM)⁻¹ ≤ ∑ wᵢ/zᵢ  →  (∑ wᵢ/zᵢ)⁻¹ ≤ GM
    have h_sum_pos : 0 < ∑ i ∈ s, w i * (z i)⁻¹ :=
      lt_of_lt_of_le (inv_pos.mpr hGM_pos) amgm_inv
    rwa [inv_le_comm₀ h_sum_pos hGM_pos]
  · -- GM ≤ AM: directly from Mathlib
    exact Real.geom_mean_le_arith_mean_weighted s w z hw hw' (fun i hi => le_of_lt (hz i hi))

/-
## Summary

### The Power Mean Limit Theorem:
lim_{r→0} M_r(z,w) = GM(z,w) = ∏ zᵢ^wᵢ

### Proved (0 sorries):
1. `sum_weighted_rpow_pos` — ∑ wᵢ zᵢ^r > 0 when ∑ wᵢ = 1 and zᵢ > 0
2. `hasDerivAt_sum_weighted_rpow_zero` — d/dr[∑ wᵢ zᵢ^r]|_{r=0} = ∑ wᵢ log zᵢ
3. `log_sum_weighted_rpow_zero` — log(∑ wᵢ zᵢ^0) = 0 when ∑ wᵢ = 1
4. `hasDerivAt_log_sum_weighted_rpow` — HasDerivAt for log ∘ (∑ wᵢ zᵢ^r)
5. `tendsto_log_sum_div_rpow` — (log ∑ wᵢ zᵢ^r) / r → ∑ wᵢ log zᵢ
6. `geomMean_eq_exp_sum_log` — GM = exp(∑ wᵢ log zᵢ)
7. `powerMean_one_eq_arithMean` — M₁ = AM (rpow_one identity)
8. `powerMean_eq_exp_log` — M_r = exp(log(∑ wᵢ zᵢ^r)/r) for r ≠ 0
9. `tendsto_powerMean_zero` — Main theorem: M_r → GM
10. `powerMean_neg1_le_geomMean_le_arithMean` — HM ≤ GM ≤ AM

### Key Insight:
The limit lim_{r→0} M_r = GM follows from the definition of derivative applied to
f(r) = log(∑ wᵢ zᵢ^r): since f(0) = 0 and f'(0) = ∑ wᵢ log zᵢ, the ratio
f(r)/r converges to f'(0), and exp of this limit equals ∏ zᵢ^wᵢ = GM.
-/
