/-
Proof: Irrationality of ∛7
Generated: 2025-12-30
Pattern: nrt-irrational
Method: Template-based derivation
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∛7

## Strategy
If x^n = m (integer) and x is not an integer, then x is irrational.

For ∛7: x = 7^(1/3), n = 3, m = 7
- (7^(1/3))^3 = 7
- 7 is not a perfect three power (1^3=1 < 7 < 8=2^3)
- Therefore 7^(1/3) is not an integer
- Therefore ∛7 is irrational
-/

namespace CubeRoot7Irrational

-- The three root of 7
noncomputable def cbrt7 : ℝ := (7 : ℝ) ^ (1/3 : ℝ)

-- Key property: (7^(1/3))^3 = 7
theorem cbrt7_pow : cbrt7 ^ 3 = 7 := by
  unfold cbrt7
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 7)]
  norm_num

-- 7 is not a perfect three power
theorem seven_not_perfect_three_power : ¬ ∃ (n : ℤ), n ^ 3 = 7 := by
  intro ⟨n, hn⟩
  have h1 : 0 < n := by
    by_contra h
    push_neg at h
    have hn_pow : n ^ 3 ≤ 0 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]
      nlinarith
    omega
  have h2 : n < 2 := by
    by_contra h
    push_neg at h
    have hn_pow : n ^ 3 ≥ 8 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]
      nlinarith
    omega
  -- Eliminate remaining candidates
  interval_cases n <;> norm_num at hn

-- cbrt7 is not an integer
theorem cbrt7_not_int : ¬ ∃ (n : ℤ), cbrt7 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = 7 := by
    have h1 : cbrt7 ^ 3 = 7 := cbrt7_pow
    rw [hn] at h1
    exact_mod_cast h1
  exact seven_not_perfect_three_power ⟨n, h⟩

-- Main theorem: ∛7 is irrational
theorem irrational_cbrt7 : Irrational cbrt7 := by
  apply irrational_nrt_of_notint_nrt 3 7
  · exact_mod_cast cbrt7_pow
  · exact cbrt7_not_int
  · norm_num

-- Alternative form
theorem irrational_7_pow_one_three : Irrational ((7 : ℝ) ^ (1/3 : ℝ)) :=
  irrational_cbrt7

end CubeRoot7Irrational
