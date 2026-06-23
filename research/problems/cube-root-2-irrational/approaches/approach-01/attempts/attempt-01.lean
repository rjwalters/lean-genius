/-
Attempt: 01
Date: 2025-12-30
Hypothesis: Prime Multiplicity Approach (via not-integer)
Goal: Prove Irrational ((2 : ℝ) ^ (1/3 : ℝ))
Status: SUCCESS ✓
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∛2

We prove that the cube root of 2 is irrational using
`irrational_nrt_of_notint_nrt` from Mathlib.

## Strategy
If x^n = m (integer) and x is not an integer, then x is irrational.

For ∛2: x = 2^(1/3), n = 3, m = 2
- (2^(1/3))^3 = 2 ✓
- 2 is not a perfect cube (no integer n satisfies n³ = 2)
- Therefore 2^(1/3) is not an integer
- Therefore ∛2 is irrational

## Key Insight
Used `nlinarith` to prove n³ bounds:
- n ≤ 0 → n³ ≤ 0 < 2 (rewrite n³ as n*n*n for nlinarith)
- n ≥ 2 → n³ ≥ 8 > 2 (same approach)
- Only n=1 remains, but 1³=1≠2
-/

namespace CubeRoot2Irrational

-- The cube root of 2
noncomputable def cbrt2 : ℝ := (2 : ℝ) ^ (1/3 : ℝ)

-- Key property: (2^(1/3))^3 = 2
theorem cbrt2_cubed : cbrt2 ^ 3 = 2 := by
  unfold cbrt2
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

-- 2 is not a perfect cube
-- This is the key number-theoretic fact: there's no integer n with n³ = 2
theorem two_not_perfect_cube : ¬ ∃ (n : ℤ), n ^ 3 = 2 := by
  intro ⟨n, hn⟩
  -- We'll show n can't be any integer by checking bounds
  -- For n ≤ 0: n³ ≤ 0 < 2
  -- For n = 1: n³ = 1 ≠ 2
  -- For n ≥ 2: n³ ≥ 8 > 2
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
  -- So n = 1, but 1³ = 1 ≠ 2
  have : n = 1 := by omega
  rw [this] at hn
  norm_num at hn

-- cbrt2 is not an integer
theorem cbrt2_not_int : ¬ ∃ (n : ℤ), cbrt2 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = 2 := by
    have h1 : cbrt2 ^ 3 = 2 := cbrt2_cubed
    rw [hn] at h1
    exact_mod_cast h1
  exact two_not_perfect_cube ⟨n, h⟩

-- Main theorem: ∛2 is irrational
theorem irrational_cbrt2 : Irrational cbrt2 := by
  apply irrational_nrt_of_notint_nrt 3 2
  · -- Prove cbrt2 ^ 3 = 2
    exact_mod_cast cbrt2_cubed
  · -- Prove cbrt2 is not an integer
    exact cbrt2_not_int
  · -- Prove 3 > 0
    norm_num

-- The form used in other files (e.g., GelfondSchneider.lean)
theorem irrational_two_pow_one_third : Irrational ((2 : ℝ) ^ (1/3 : ℝ)) :=
  irrational_cbrt2

end CubeRoot2Irrational
