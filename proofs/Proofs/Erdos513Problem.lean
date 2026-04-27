/-
# Erdős Problem #513: Maximum Term of a Power Series

For a transcendental entire function f(z) = Σ aₙzⁿ, define:
  μ(r) = max_n |aₙ rⁿ|       (maximum term)
  M(r) = max_{|z|=r} |f(z)|   (maximum modulus)

Determine the greatest possible value of
  liminf_{r→∞} μ(r) / M(r)
over all transcendental entire functions.

Known:
- The value exceeds 1/2 (Kövári, unpublished)
- The value is at most 2/π - c for some c > 0 (Clunie–Hayman, 1964)
- Trivially lies in [0, 1]

Status: OPEN.

Reference: https://erdosproblems.com/513
-/

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Order.LiminfLimsup

/- ## Definitions -/

/-- The maximum term μ(r, f) = sup_n |aₙ| · rⁿ for a power series with
    coefficients given by `a : ℕ → ℂ`. Wraps with `max 0` to guarantee
    nonnegativity even when the iSup is ill-defined (unbounded range). -/
noncomputable def maxTerm (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  max 0 (⨆ n : ℕ, ‖a n‖ * max r 0 ^ n)

/-- maxTerm is nonneg for r ≥ 0. -/
theorem maxTerm_nonneg (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ maxTerm a r :=
  le_max_left 0 _

/-- The entire function defined by a power series with coefficients `a`.
    For coefficients defining a non-summable series at `z`, `tsum` returns 0. -/
noncomputable def powerSeriesFun (a : ℕ → ℂ) (z : ℂ) : ℂ := ∑' n, a n * z ^ n

/-- The maximum modulus M(r, f) = sup_{|z|=r} |f(z)| for the entire
    function defined by `a`. Wraps with `max 0` to guarantee nonnegativity
    (the iSup over the sphere is already nonneg, but this avoids needing
    boundedness assumptions on `a`). -/
noncomputable def maxModulus (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  max 0 (⨆ z ∈ Metric.sphere (0 : ℂ) r, ‖powerSeriesFun a z‖)

/-- maxModulus is nonneg for r ≥ 0 (in fact for all r, by definition). -/
theorem maxModulus_nonneg (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ maxModulus a r :=
  le_max_left 0 _

/-- The ratio μ(r)/M(r). Returns 0 if M(r) = 0. -/
noncomputable def termModulusRatio (a : ℕ → ℂ) (r : ℝ) : ℝ :=
  if maxModulus a r = 0 then 0
  else maxTerm a r / maxModulus a r

/-- A sequence of coefficients defines a transcendental entire function:
    the power series converges everywhere, and it is not a polynomial. -/
def IsTranscendentalEntire (a : ℕ → ℂ) : Prop :=
  (∀ N : ℕ, ∃ n : ℕ, n > N ∧ a n ≠ 0)

/- ## Known Results (Axiomatized) -/

/-- μ(r) ≤ M(r) always holds, so the ratio is at most 1. -/
axiom maxTerm_le_maxModulus (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
  maxTerm a r ≤ maxModulus a r

/-- Kövári's lower bound: there exists a transcendental entire function whose
    liminf of the ratio exceeds 1/2. -/
axiom kovari_lower_bound :
  ∃ a : ℕ → ℂ, IsTranscendentalEntire a ∧
    (1 : ℝ) / 2 < Filter.liminf (fun r => termModulusRatio a r) Filter.atTop

/-- Clunie–Hayman upper bound (1964): for every transcendental entire
    function, liminf_{r→∞} μ(r)/M(r) ≤ 2/π - c for some absolute c > 0. -/
axiom clunie_hayman_upper_bound :
  ∃ c : ℝ, 0 < c ∧
    ∀ a : ℕ → ℂ, IsTranscendentalEntire a →
      Filter.liminf (fun r => termModulusRatio a r) Filter.atTop ≤ 2 / Real.pi - c

/- ## Proved Structural Theorems -/

/-- The term-modulus ratio is always nonneg for r ≥ 0. -/
theorem termModulusRatio_nonneg (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    0 ≤ termModulusRatio a r := by
  unfold termModulusRatio
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (maxTerm_nonneg a r hr)
      (le_of_lt (lt_of_le_of_ne (maxModulus_nonneg a r hr) (Ne.symm h)))

/-- The term-modulus ratio is at most 1 for r ≥ 0. -/
theorem termModulusRatio_le_one (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    termModulusRatio a r ≤ 1 := by
  unfold termModulusRatio
  split_ifs with h
  · exact zero_le_one
  · rw [div_le_one (lt_of_le_of_ne (maxModulus_nonneg a r hr) (Ne.symm h))]
    exact maxTerm_le_maxModulus a r hr

/-- The term-modulus ratio lies in [0, 1] for r ≥ 0. -/
theorem termModulusRatio_mem_Icc (a : ℕ → ℂ) (r : ℝ) (hr : 0 ≤ r) :
    termModulusRatio a r ∈ Set.Icc 0 1 :=
  ⟨termModulusRatio_nonneg a r hr, termModulusRatio_le_one a r hr⟩

/-- When M(r) = 0, the ratio is exactly 0 (by definition). -/
theorem termModulusRatio_eq_zero_of_maxModulus_eq_zero (a : ℕ → ℂ) (r : ℝ)
    (h : maxModulus a r = 0) : termModulusRatio a r = 0 := by
  unfold termModulusRatio
  simp [h]

/-- When M(r) > 0, the ratio equals the actual quotient μ(r)/M(r). -/
theorem termModulusRatio_eq_div (a : ℕ → ℂ) (r : ℝ)
    (h : 0 < maxModulus a r) :
    termModulusRatio a r = maxTerm a r / maxModulus a r := by
  unfold termModulusRatio
  simp [ne_of_gt h]

/-- The known bounds 1/2 and 2/π are consistent: 1/2 < 2/π.
    This ensures the interval in which the answer lies is non-empty. -/
theorem half_lt_two_div_pi : (1 : ℝ) / 2 < 2 / Real.pi := by
  have h1 := Real.pi_pos
  have h2 : Real.pi < 4 := by linarith [Real.pi_lt_four]
  have h3 : 0 < Real.pi * 2 := by positivity
  have h5 : 1 / 2 * (Real.pi * 2) = Real.pi := by ring
  have h6 : 2 / Real.pi * (Real.pi * 2) = 4 := by
    have : Real.pi ≠ 0 := ne_of_gt h1
    field_simp; ring
  nlinarith

/-- The supremum of liminf ratios exceeds 1/2 (from Kövári). -/
theorem supremum_exceeds_half :
    ∃ a : ℕ → ℂ, IsTranscendentalEntire a ∧
      (1 : ℝ) / 2 < Filter.liminf (fun r => termModulusRatio a r) Filter.atTop :=
  kovari_lower_bound

/-- The supremum of liminf ratios is strictly less than 2/π (from Clunie–Hayman). -/
theorem supremum_lt_two_div_pi :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ → ℂ, IsTranscendentalEntire a →
      Filter.liminf (fun r => termModulusRatio a r) Filter.atTop < 2 / Real.pi := by
  obtain ⟨c, hc, hbound⟩ := clunie_hayman_upper_bound
  exact ⟨c, hc, fun a ha => lt_of_le_of_lt (hbound a ha) (by linarith)⟩

/-- The Clunie–Hayman bound gives a gap: every transcendental entire function
    has liminf ratio bounded away from 2/π by an absolute constant. -/
theorem clunie_hayman_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ → ℂ, IsTranscendentalEntire a →
      Filter.liminf (fun r => termModulusRatio a r) Filter.atTop + c ≤ 2 / Real.pi := by
  obtain ⟨c, hc, hbound⟩ := clunie_hayman_upper_bound
  exact ⟨c, hc, fun a ha => by linarith [hbound a ha]⟩

/- ## The Open Question -/

/-- Erdős Problem #513: Determine the exact value of
    sup { liminf_{r→∞} μ(r)/M(r) : f transcendental entire }.
    Formalized as the assertion that this supremum exists in (1/2, 2/π). -/
axiom erdos_513_exact_value :
  ∃ L : ℝ, (1 : ℝ) / 2 < L ∧ L < 2 / Real.pi ∧
    (∀ a : ℕ → ℂ, IsTranscendentalEntire a →
      Filter.liminf (fun r => termModulusRatio a r) Filter.atTop ≤ L) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ a : ℕ → ℂ, IsTranscendentalEntire a ∧
        L - ε < Filter.liminf (fun r => termModulusRatio a r) Filter.atTop)
