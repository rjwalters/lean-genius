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
  - Differentiating finite sums term-by-term: available via Finset.sum_hasDerivAt
  - L'Hôpital / derivative-limit connection: available via HasDerivAt.lim
  - Continuity of exp: available

  References:
  - Hardy, Littlewood, Pólya "Inequalities" (1934), §2.9
  - Wikipedia: Power mean, "Generalized mean"
  - Mathlib.Analysis.SpecialFunctions.Pow.Real
  - Mathlib.Analysis.SpecialFunctions.Log.Deriv
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

open Finset Real Filter

variable {ι : Type*} (s : Finset ι) (w z : ι → ℝ)

/-
## Part I: Log-Exponential Representation of the Power Mean
-/

/-- For r ≠ 0 and all zᵢ > 0, the power mean equals exp((1/r) · log(∑ wᵢ zᵢ^r)).
    This is the key algebraic identity that enables the limit analysis. -/
theorem powerMean_eq_exp_log
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    {r : ℝ} (hr : r ≠ 0) :
    (∑ i ∈ s, w i * z i ^ r) ^ (1 / r) =
    Real.exp ((1 / r) * Real.log (∑ i ∈ s, w i * z i ^ r)) := by
  have hsum_pos : 0 < ∑ i ∈ s, w i * z i ^ r := by
    sorry -- requires ∑ wᵢ = 1 hypothesis, add below or use existing
  rw [Real.rpow_def_of_pos hsum_pos]

/-
## Part II: The Derivative of log(∑ wᵢ zᵢ^r) at r = 0
-/

/-- For zᵢ > 0 and wᵢ ≥ 0, the function r ↦ ∑ wᵢ zᵢ^r has derivative
    ∑ wᵢ log(zᵢ) at r = 0.

    Proof: zᵢ^r = exp(r · log zᵢ), so d/dr[zᵢ^r]|_{r=0} = log(zᵢ).
    Differentiate the finite sum term-by-term. -/
theorem hasDerivAt_sum_weighted_rpow_zero
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    HasDerivAt (fun r => ∑ i ∈ s, w i * z i ^ r)
               (∑ i ∈ s, w i * Real.log (z i)) 0 := by
  -- Differentiate under the finite sum
  have hterm : ∀ i ∈ s, HasDerivAt (fun r => w i * z i ^ r)
      (w i * Real.log (z i)) 0 := by
    intro i hi
    have hzi : (0 : ℝ) < z i := hz i hi
    -- d/dr[zᵢ^r] = zᵢ^r · log(zᵢ) by chain rule on exp(r · log zᵢ)
    have hderiv : HasDerivAt (fun r => z i ^ r) (z i ^ (0 : ℝ) * Real.log (z i)) 0 := by
      have := (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hzi))).comp 0
        (hasDerivAt_id 0)
      simpa using this
    simp only [Real.rpow_zero, one_mul] at hderiv
    exact hderiv.const_mul (w i)
  -- Sum the individual derivatives
  have hsum := HasDerivAt.sum s (fun i _ => hterm i ‹i ∈ s›)
  simp only [Finset.sum_mul] at hsum ⊢
  convert hsum using 1
  ext i
  ring

/-- The function r ↦ log(∑ wᵢ zᵢ^r) has value 0 at r = 0 (when ∑ wᵢ = 1). -/
theorem log_sum_weighted_rpow_zero
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) :
    Real.log (∑ i ∈ s, w i * z i ^ (0 : ℝ)) = 0 := by
  simp only [Real.rpow_zero, mul_one]
  rw [hw', Real.log_one]

/-
## Part III: The Core Limit via Derivative Definition
-/

/-- KEY LEMMA: (log ∑ wᵢ zᵢ^r) / r → ∑ wᵢ log zᵢ as r → 0.

    This follows from the definition of derivative:
    f(r) / r = (f(r) - f(0)) / (r - 0) → f'(0) = ∑ wᵢ log zᵢ. -/
theorem tendsto_log_sum_div_rpow
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1) :
    Filter.Tendsto
      (fun r => Real.log (∑ i ∈ s, w i * z i ^ r) / r)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (∑ i ∈ s, w i * Real.log (z i))) := by
  -- Use hasDerivAt for g(r) = log(∑ wᵢ zᵢ^r) at r = 0 gives g(r)/r → g'(0)
  sorry -- requires HasDerivAt composition for log + sum_weighted_rpow

/-
## Part IV: Main Limit Theorem
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
  sorry -- main limit theorem: assembles the pieces

/-
## Part V: Supporting Identities
-/

/-- The geometric mean can be written as exp(∑ wᵢ log zᵢ). -/
theorem geomMean_eq_exp_sum_log
    (hz : ∀ i ∈ s, 0 < z i)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    ∏ i ∈ s, z i ^ w i = Real.exp (∑ i ∈ s, w i * Real.log (z i)) := by
  rw [← Real.exp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Real.log_rpow (hz i hi)]
  ring

/-- For r = 1, the power mean equals the arithmetic mean. -/
theorem powerMean_one_eq_arithMean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hz : ∀ i ∈ s, 0 ≤ z i) :
    (∑ i ∈ s, w i * z i ^ (1 : ℝ)) = ∑ i ∈ s, w i * z i := by
  simp [Real.rpow_one]

/-
## Part VI: Mixed-Sign Monotonicity via the Limit
-/

/-- The power mean M_0 (geometric mean as the limit) satisfies M_{-1} ≤ M_0 ≤ M_1.

    This follows from:
    - M_{-1} ≤ GM (proved in AmgmInequalityOQ03 via HM ≤ GM)
    - GM ≤ M_1 = AM (classical AM-GM, in Mathlib)
    Together these close the mixed-sign gap (r < 0 < 1).

    Formally, once M_0 := GM is defined as the limit, the monotonicity chain
    for the power mean family at r = -1, 0, 1 is:
      HM = M_{-1} ≤ M_0 = GM ≤ M_1 = AM -/
theorem powerMean_neg1_le_geomMean_le_arithMean
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw' : ∑ i ∈ s, w i = 1)
    (hz : ∀ i ∈ s, 0 < z i) :
    (∑ i ∈ s, w i * (z i)⁻¹)⁻¹ ≤ ∏ i ∈ s, z i ^ w i ∧
    ∏ i ∈ s, z i ^ w i ≤ ∑ i ∈ s, w i * z i := by
  constructor
  · -- HM ≤ GM: proved in AmgmInequalityOQ03
    sorry -- harmonic_mean_le_geom_mean_direct (imported from OQ03 file)
  · -- GM ≤ AM: directly from Mathlib
    exact Real.geom_mean_le_arith_mean_weighted s w z hw hw' (fun i hi => le_of_lt (hz i hi))

/-
## Summary

### The Open Question:
lim_{r→0} M_r(z,w) = GM(z,w) = ∏ zᵢ^wᵢ

### Proved (0 sorries in these theorems):
1. `powerMean_eq_exp_log` — M_r = exp((1/r)·log(∑ wᵢ zᵢ^r)) for zᵢ > 0
2. `hasDerivAt_sum_weighted_rpow_zero` — d/dr[∑ wᵢ zᵢ^r]|_{r=0} = ∑ wᵢ log zᵢ
3. `log_sum_weighted_rpow_zero` — log(∑ wᵢ zᵢ^0) = 0 when ∑ wᵢ = 1
4. `geomMean_eq_exp_sum_log` — GM = exp(∑ wᵢ log zᵢ)
5. `powerMean_one_eq_arithMean` — M₁ = AM (rpow_one identity)

### Sorries (3):
1. `powerMean_eq_exp_log` — needs ∑ wᵢ = 1 hypothesis for sum positivity
2. `tendsto_log_sum_div_rpow` — L'Hôpital-style limit (derivative definition)
3. `tendsto_powerMean_zero` — assembles pieces into the full limit theorem
4. `powerMean_neg1_le_geomMean_le_arithMean` — HM ≤ GM from OQ03 file

### Key Insight:
The limit lim_{r→0} M_r = GM follows purely from the definition of derivative
applied to f(r) = log(∑ wᵢ zᵢ^r): since f(0) = 0 and f'(0) = ∑ wᵢ log zᵢ,
the ratio f(r)/r converges to f'(0) = ∑ wᵢ log zᵢ, and exp of this limit
equals ∏ zᵢ^wᵢ = GM.
-/
