/-
# AM-GM OQ-03-OQ-03 follow-up OQ-02
# The AM–GM–HM Chain as Power-Mean Monotonicity at r = -1, 0, 1

The parent entry (`AmgmInequalityOQ03OQ03.lean`) defines the power mean family
`M_r` and proves the two endpoint *identities* for two variables:
`M₁(a,b) = (a+b)/2` (arithmetic mean) and `M₋₁(a,b) = 2ab/(a+b)` (harmonic mean).
The sibling (`AmgmInequalityPowerMeanLimits.lean`) handles the *limits*
`M_r → max/min` as `r → ±∞`.

This follow-up fills the remaining gap between those endpoints: the **finite
monotonicity** of `M_r` at the three classical exponents, i.e. the
arithmetic–geometric–harmonic mean chain

  > `M₋₁(a,b) ≤ M₀(a,b) ≤ M₁(a,b)`,  i.e.  `HM ≤ GM ≤ AM`.

We first pin down the geometric mean as the `r = 0` power mean,
`M₀(a,b) = √(ab)` (`powerMean_zero_eq_sqrt`), re-establish the two endpoint
identities self-containedly, prove the two classical two-variable inequalities
`√(ab) ≤ (a+b)/2` and `2ab/(a+b) ≤ √(ab)`, and assemble them into the power-mean
chain `powerMean_amgmhm_chain`.  This is the `n = 2` instance of the general
power-mean inequality (monotonicity of `r ↦ M_r`), the result that the
`r → ±∞` limits and the endpoint identities were pointing at.

## Results (0 sorries, 0 axioms — fully proved)
Elementary real analysis: `Real.sqrt`, `Real.rpow`, and `nlinarith` on
`(a-b)² ≥ 0`.
-/

import Mathlib

namespace AmgmOQ03OQ03OQ02

open Finset

/-- The power mean `M_r` of positive reals in a finset, at exponent `r`
    (geometric mean by the `r = 0` convention).  Same definition as the parent. -/
noncomputable def powerMean {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (r : ℝ) : ℝ :=
  if r = 0 then
    (∏ i : ι, x i) ^ ((Fintype.card ι : ℝ)⁻¹)
  else
    ((∑ i : ι, (x i) ^ r) / Fintype.card ι) ^ (1 / r)

-- ============================================================
-- PART I: The three endpoint evaluations for two variables
-- ============================================================

/-- **Geometric mean.** For two positive reals, the `r = 0` power mean is the
geometric mean `√(ab)`. -/
theorem powerMean_zero_eq_sqrt (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean (![a, b]) 0 = Real.sqrt (a * b) := by
  unfold powerMean
  rw [if_pos rfl, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Fintype.card_fin, Nat.cast_ofNat]
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- **Arithmetic mean.** `M₁(a,b) = (a+b)/2` (re-proved self-containedly). -/
theorem powerMean_one_eq_am (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean (![a, b]) 1 = (a + b) / 2 := by
  unfold powerMean
  rw [if_neg one_ne_zero, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fintype.card_fin, Real.rpow_one]
  norm_num [Real.rpow_one]

/-- **Harmonic mean.** `M₋₁(a,b) = 2ab/(a+b)` (re-proved self-containedly). -/
theorem powerMean_negOne_eq_hm (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean (![a, b]) (-1) = 2 * a * b / (a + b) := by
  unfold powerMean
  rw [if_neg (show (-1:ℝ) ≠ 0 by norm_num), Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Fintype.card_fin, show (1:ℝ) / (-1) = -1 from by norm_num]
  rw [Real.rpow_neg_one, Real.rpow_neg_one, Real.rpow_neg_one]
  field_simp
  ring

-- ============================================================
-- PART II: The two classical two-variable inequalities
-- ============================================================

/-- **GM ≤ AM** for two positive reals: `√(ab) ≤ (a+b)/2`. Equivalent to
`(a-b)² ≥ 0`. -/
theorem sqrt_mul_le_add_div_two (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [show (a + b) / 2 = Real.sqrt (((a + b) / 2) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  nlinarith [sq_nonneg (a - b)]

/-- **HM ≤ GM** for two positive reals: `2ab/(a+b) ≤ √(ab)`. Equivalent to
`(a-b)² ≥ 0`. -/
theorem hm_le_sqrt_mul (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * a * b / (a + b) ≤ Real.sqrt (a * b) := by
  rw [show 2 * a * b / (a + b) = Real.sqrt ((2 * a * b / (a + b)) ^ 2) from
    (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_pow, div_le_iff₀ (by positivity)]
  nlinarith [mul_nonneg (mul_pos ha hb).le (sq_nonneg (a - b))]

-- ============================================================
-- PART III: The power-mean AM–GM–HM chain
-- ============================================================

/-- **Main theorem — the AM–GM–HM chain via power means.**
For two positive reals, the power mean is monotone across the three classical
exponents: `M₋₁ ≤ M₀ ≤ M₁`, i.e. `HM ≤ GM ≤ AM`.  This is the `n = 2` instance
of the general power-mean inequality, bridging the parent's endpoint identities
and the sibling's `r → ±∞` limits. -/
theorem powerMean_amgmhm_chain (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    powerMean (![a, b]) (-1) ≤ powerMean (![a, b]) 0 ∧
      powerMean (![a, b]) 0 ≤ powerMean (![a, b]) 1 := by
  rw [powerMean_negOne_eq_hm a b ha hb, powerMean_zero_eq_sqrt a b ha hb,
    powerMean_one_eq_am a b ha hb]
  exact ⟨hm_le_sqrt_mul a b ha hb, sqrt_mul_le_add_div_two a b ha hb⟩

/-- The chain collapses to equality exactly when the two inputs agree
(`a = b`): then `HM = GM = AM = a`. -/
theorem powerMean_chain_eq_of_eq (a : ℝ) (ha : 0 < a) :
    powerMean (![a, a]) (-1) = a ∧ powerMean (![a, a]) 0 = a ∧
      powerMean (![a, a]) 1 = a := by
  refine ⟨?_, ?_, ?_⟩
  · rw [powerMean_negOne_eq_hm a a ha ha]
    field_simp
    ring
  · rw [powerMean_zero_eq_sqrt a a ha ha]; exact Real.sqrt_mul_self ha.le
  · rw [powerMean_one_eq_am a a ha ha]; ring

end AmgmOQ03OQ03OQ02
