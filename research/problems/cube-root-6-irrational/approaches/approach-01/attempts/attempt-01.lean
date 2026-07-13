/-
Proof: Irrationality of ∛6
Generated: 2025-12-30
Pattern: nrt-irrational
Method: Template-based derivation
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∛6

## Strategy
If x^n = m (integer) and x is not an integer, then x is irrational.

For ∛6: x = 6^(1/3), n = 3, m = 6
- (6^(1/3))^3 = 6
- 6 is not a perfect three power (1^3=1 < 6 < 8=2^3)
- Therefore 6^(1/3) is not an integer
- Therefore ∛6 is irrational
-/

namespace CubeRoot6Irrational

-- The three root of 6
noncomputable def cbrt6 : ℝ := (6 : ℝ) ^ (1/3 : ℝ)

-- Key property: (6^(1/3))^3 = 6
theorem cbrt6_pow : cbrt6 ^ 3 = 6 := by
  unfold cbrt6
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 6)]
  norm_num

-- 6 is not a perfect three power
theorem six_not_perfect_three_power : ¬ ∃ (n : ℤ), n ^ 3 = 6 := by
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

-- cbrt6 is not an integer
theorem cbrt6_not_int : ¬ ∃ (n : ℤ), cbrt6 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = 6 := by
    have h1 : cbrt6 ^ 3 = 6 := cbrt6_pow
    rw [hn] at h1
    exact_mod_cast h1
  exact six_not_perfect_three_power ⟨n, h⟩

-- Main theorem: ∛6 is irrational
theorem irrational_cbrt6 : Irrational cbrt6 := by
  apply irrational_nrt_of_notint_nrt 3 6
  · exact_mod_cast cbrt6_pow
  · exact cbrt6_not_int
  · norm_num

-- Alternative form
theorem irrational_6_pow_one_three : Irrational ((6 : ℝ) ^ (1/3 : ℝ)) :=
  irrational_cbrt6

end CubeRoot6Irrational
