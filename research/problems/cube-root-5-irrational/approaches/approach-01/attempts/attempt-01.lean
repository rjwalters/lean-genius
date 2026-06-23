/-
Attempt: 01
Date: 2025-12-30
Hypothesis: n-th Root Irrationality Pattern (derived from cube-root-2-irrational)
Goal: Prove Irrational ((5 : ℝ) ^ (1/3 : ℝ))
Status: DERIVED (needs verification)
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∛5

Derived from cube-root-2-irrational using the n-th root irrationality pattern.

## Strategy
If x^n = m (integer) and x is not an integer, then x is irrational.

For ∛5: x = 5^(1/3), n = 3, m = 5
- (5^(1/3))^3 = 5 ✓
- 5 is not a perfect cube (1³=1 < 5 < 8=2³)
- Therefore 5^(1/3) is not an integer
- Therefore ∛5 is irrational
-/

namespace CubeRoot5Irrational

-- The cube root of 5
noncomputable def cbrt5 : ℝ := (5 : ℝ) ^ (1/3 : ℝ)

-- Key property: (5^(1/3))^3 = 5
theorem cbrt5_cubed : cbrt5 ^ 3 = 5 := by
  unfold cbrt5
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

-- 5 is not a perfect cube (1³=1 < 5 < 8=2³)
theorem five_not_perfect_cube : ¬ ∃ (n : ℤ), n ^ 3 = 5 := by
  intro ⟨n, hn⟩
  have h1 : 0 < n := by
    by_contra h
    push_neg at h
    have hn3 : n ^ 3 ≤ 0 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]
      nlinarith
    omega
  have h2 : n < 2 := by
    by_contra h
    push_neg at h
    have hn3 : n ^ 3 ≥ 8 := by
      have : n ^ 3 = n * n * n := by ring
      rw [this]
      nlinarith
    omega
  -- So n = 1, but 1³ = 1 ≠ 5
  have : n = 1 := by omega
  rw [this] at hn
  norm_num at hn

-- cbrt5 is not an integer
theorem cbrt5_not_int : ¬ ∃ (n : ℤ), cbrt5 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = 5 := by
    have h1 : cbrt5 ^ 3 = 5 := cbrt5_cubed
    rw [hn] at h1
    exact_mod_cast h1
  exact five_not_perfect_cube ⟨n, h⟩

-- Main theorem: ∛5 is irrational
theorem irrational_cbrt5 : Irrational cbrt5 := by
  apply irrational_nrt_of_notint_nrt 3 5
  · exact_mod_cast cbrt5_cubed
  · exact cbrt5_not_int
  · norm_num

-- Alternative form
theorem irrational_five_pow_one_third : Irrational ((5 : ℝ) ^ (1/3 : ℝ)) :=
  irrational_cbrt5

end CubeRoot5Irrational
