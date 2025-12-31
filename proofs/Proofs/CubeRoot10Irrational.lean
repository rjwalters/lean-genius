/-
Proof: Irrationality of ∛10
Generated: 2025-12-30
Pattern: nrt-irrational
Method: Template-based derivation
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∛10

## Strategy
If x^n = m (integer) and x is not an integer, then x is irrational.

For ∛10: x = 10^(1/3), n = 3, m = 10
- (10^(1/3))^3 = 10
- 10 is not a perfect three power (2^3=8 < 10 < 27=3^3)
- Therefore 10^(1/3) is not an integer
- Therefore ∛10 is irrational
-/

namespace CubeRoot10Irrational

-- The three root of 10
noncomputable def cbrt10 : ℝ := (10 : ℝ) ^ (1/3 : ℝ)

-- Key property: (10^(1/3))^3 = 10
theorem cbrt10_pow : cbrt10 ^ 3 = 10 := by
  unfold cbrt10
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
  norm_num

-- 10 is not a perfect three power
theorem ten_not_perfect_three_power : ¬ ∃ (n : ℤ), n ^ 3 = 10 := by
  intro ⟨n, hn⟩
  have h1 : 0 < n := by
    by_contra h
    push_neg at h
    have hn_pow : n ^ 3 ≤ 0 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]
      nlinarith
    omega
  have h2 : n < 3 := by
    by_contra h
    push_neg at h
    have hn_pow : n ^ 3 ≥ 27 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]
      nlinarith
    omega
  -- Eliminate remaining candidates
  interval_cases n <;> norm_num at hn

-- cbrt10 is not an integer
theorem cbrt10_not_int : ¬ ∃ (n : ℤ), cbrt10 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = 10 := by
    have h1 : cbrt10 ^ 3 = 10 := cbrt10_pow
    rw [hn] at h1
    exact_mod_cast h1
  exact ten_not_perfect_three_power ⟨n, h⟩

-- Main theorem: ∛10 is irrational
theorem irrational_cbrt10 : Irrational cbrt10 := by
  apply irrational_nrt_of_notint_nrt 3 10
  · exact_mod_cast cbrt10_pow
  · exact cbrt10_not_int
  · norm_num

-- Alternative form
theorem irrational_10_pow_one_three : Irrational ((10 : ℝ) ^ (1/3 : ℝ)) :=
  irrational_cbrt10

end CubeRoot10Irrational
