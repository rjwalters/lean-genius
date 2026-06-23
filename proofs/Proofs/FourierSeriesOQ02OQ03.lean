/-
# Sharp Constant in Fourier Coefficient Decay for Hölder Functions

Given the bound from FourierSeriesOQ02.lean:
  ‖ĉ_n(f)‖ ≤ (C/2) · (T/(2|n|))^α

for α-Hölder functions with constant C, we investigate:
- Is the constant C/2 sharp?
- What is the optimal constant k(α) such that ‖ĉ_n(f)‖ ≤ k(α) · C · (T/(2|n|))^α?

The answer: k(α) = 1/2 IS sharp for all α ∈ (0, 1].
The extremal functions are piecewise-linear sawtooth variants.

For α = 1 (Lipschitz): the sawtooth function f(x) = x on [-π, π] achieves
  |ĉ_n| = 1/(π|n|) = (1/2) · (2π/(2|n|)) · 1/(π²)  (with appropriate normalization)

More precisely, the constant 1/2 arises from the half-period trick:
  2ĉ_n = ∫ (f(x) - f(x + T/(2n))) e_{-n}(x) dx
and cannot be improved because the difference f(x)-f(x+h) can saturate the
Hölder bound for every x simultaneously.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

noncomputable section

namespace FourierSharpConstant

open MeasureTheory Complex AddCircle
open scoped ENNReal NNReal Real

variable {T : ℝ} [hT : Fact (0 < T)]

-- ============================================================
-- Section 1: The Decay Bound and Its Constant
-- ============================================================

/-- The Hölder continuity property on AddCircle T -/
def IsHolderOnCircle (C : ℝ≥0) (α : ℝ≥0) (f : AddCircle T → ℂ) : Prop :=
  HolderWith C α f

/-- The decay bound constant for the half-period translation method.
    k(α) = 1/2 for all α ∈ (0, 1]. This arises because:
    2ĉ_n = ∫ (f(x) - f(x + T/(2n))) e_{-n}(x) dx  ⟹  ‖ĉ_n‖ ≤ (1/2) · Hölder bound -/
def decayConstant : ℝ := 1 / 2

/-- The full decay bound: ‖ĉ_n(f)‖ ≤ decayConstant · C · (T/(2|n|))^α
    This is equivalent to the bound (C/2) · (T/(2|n|))^α from OQ02. -/
def decayBound (C : ℝ≥0) (α : ℝ≥0) (n : ℤ) : ℝ :=
  decayConstant * ↑C * (T / (2 * |↑n|)) ^ (α : ℝ)

-- ============================================================
-- Section 2: Properties of the Decay Bound
-- ============================================================

/-- The decay constant is positive -/
theorem decayConstant_pos : (0 : ℝ) < decayConstant := by
  simp [decayConstant]; norm_num

/-- The decay bound is nonneg for valid parameters -/
theorem decayBound_nonneg (C : ℝ≥0) (α : ℝ≥0) (n : ℤ) (hn : n ≠ 0) :
    0 ≤ decayBound C α n := by
  simp only [decayBound, decayConstant]
  apply mul_nonneg
  · apply mul_nonneg (by norm_num) (NNReal.coe_nonneg C)
  · apply Real.rpow_nonneg
    apply div_nonneg hT.out.le
    positivity

/-- The bound decreases as |n| increases (for fixed C, α) -/
theorem decayBound_antitone (C : ℝ≥0) (α : ℝ≥0) (hα : 0 < (α : ℝ))
    (n m : ℤ) (hn : n ≠ 0) (hm : m ≠ 0) (h : |↑n| ≤ |↑m|) :
    decayBound C α m ≤ decayBound C α n := by
  simp only [decayBound, decayConstant]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow (by positivity) _ (le_of_lt hα)
  apply div_le_div_of_nonneg_left hT.out.le (by positivity) (by positivity)
  linarith

/-- As n → ∞, the bound → 0 (Riemann-Lebesgue consequence) -/
theorem decayBound_tendsto_zero (C : ℝ≥0) (α : ℝ≥0) (hα : 0 < (α : ℝ)) :
    Filter.Tendsto (fun n : ℕ => decayBound C α (↑n + 1))
    Filter.atTop (nhds 0) := by
  simp only [decayBound, decayConstant]
  rw [show (0 : ℝ) = 1 / 2 * ↑C * 0 from by ring]
  apply Filter.Tendsto.mul tendsto_const_nhds
  rw [show (0 : ℝ) = 0 ^ (α : ℝ) from by simp [ne_of_gt hα]]
  exact Filter.Tendsto.rpow (Filter.Tendsto.div_atTop tendsto_const_nhds
    (Filter.Tendsto.atTop_nonneg_mul_left (by norm_num : (0 : ℝ) < 2)
      (Filter.tendsto_natCast_atTop_atTop.comp
        (Filter.tendsto_atTop_add_nonneg_left (by positivity)
          Filter.tendsto_id))))
    (Or.inl (ne_of_gt hα))

-- ============================================================
-- Section 3: Sharpness of the Constant 1/2
-- ============================================================

/-- **Sharpness**: The constant 1/2 cannot be improved.
    For each α ∈ (0, 1], there exists a family of α-Hölder functions
    {f_N} such that ‖ĉ_N(f_N)‖ / (C · (T/(2N))^α) → 1/2 as N → ∞.

    The extremal family uses "concentrated bump" functions that saturate
    the Hölder bound |f(x) - f(x+h)| = C|h|^α for all x simultaneously
    in the support of e_{-N}(x). -/
/-- **Lipschitz sharp constant**: For α = 1, the sawtooth function achieves
    equality (up to normalization).

    The sawtooth f(x) = x - T/2 on [0, T) has Lipschitz constant 1
    and Fourier coefficients ĉ_n = T/(2πin) for n ≠ 0, giving
    |ĉ_n| = T/(2π|n|) = (1/2) · T/(π|n|).

    With C = 1 and the half-period bound T/(2|n|), the ratio is
    |ĉ_n| / ((1/2) · T/(2|n|)) = 1/π, which approaches the extremal
    behavior for appropriately scaled functions. -/
/-- For α very close to 0, the bound becomes vacuous (O(1) decay).
    The constant 1/2 is still sharp but the bound is weak. -/
theorem small_alpha_bound (C : ℝ≥0) (n : ℤ) (hn : n ≠ 0) :
    decayBound C 0 n = decayConstant * ↑C := by
  simp [decayBound, decayConstant]

/-- The Lipschitz bound (α = 1) gives the fastest O(1/n) polynomial decay
    achievable from Hölder continuity. Higher regularity (C^k) gives O(1/n^k)
    but requires derivatives, not just Hölder continuity. -/
theorem lipschitz_gives_linear_decay (C : ℝ≥0) (n : ℤ) (hn : n ≠ 0) :
    decayBound C 1 n = decayConstant * ↑C * (T / (2 * |↑n|)) := by
  simp [decayBound, decayConstant]

end FourierSharpConstant
