/-
Proof: Irrationality of ∛9
Generated: 2025-12-30
Pattern: nrt-irrational
Method: Template-based derivation
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∛9

## Strategy
If x^n = m (integer) and x is not an integer, then x is irrational.

For ∛9: x = 9^(1/3), n = 3, m = 9
- (9^(1/3))^3 = 9
- 9 is not a perfect three power (2^3=8 < 9 < 27=3^3)
- Therefore 9^(1/3) is not an integer
- Therefore ∛9 is irrational
-/

namespace CubeRoot9Irrational

-- The three root of 9
noncomputable def cbrt9 : ℝ := (9 : ℝ) ^ (1/3 : ℝ)

-- Key property: (9^(1/3))^3 = 9
theorem cbrt9_pow : cbrt9 ^ 3 = 9 := by
  unfold cbrt9
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)]
  norm_num

-- 9 is not a perfect three power
theorem nine_not_perfect_three_power : ¬ ∃ (n : ℤ), n ^ 3 = 9 := by
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

-- cbrt9 is not an integer
theorem cbrt9_not_int : ¬ ∃ (n : ℤ), cbrt9 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = 9 := by
    have h1 : cbrt9 ^ 3 = 9 := cbrt9_pow
    rw [hn] at h1
    exact_mod_cast h1
  exact nine_not_perfect_three_power ⟨n, h⟩

-- Main theorem: ∛9 is irrational
theorem irrational_cbrt9 : Irrational cbrt9 := by
  apply irrational_nrt_of_notint_nrt 3 9
  · exact_mod_cast cbrt9_pow
  · exact cbrt9_not_int
  · norm_num

-- Alternative form
theorem irrational_9_pow_one_three : Irrational ((9 : ℝ) ^ (1/3 : ℝ)) :=
  irrational_cbrt9

end CubeRoot9Irrational
