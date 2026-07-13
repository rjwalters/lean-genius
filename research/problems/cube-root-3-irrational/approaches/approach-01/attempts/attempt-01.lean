/-
Attempt: 01
Date: 2025-12-30
Hypothesis: Direct application of irrational_nrt_of_notint_nrt (from knowledge base)
Goal: Prove Irrational ((3 : ℝ) ^ (1/3 : ℝ))
Status: PENDING
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∛3

Direct application of the pattern from cube-root-2-irrational.
Using `irrational_nrt_of_notint_nrt` from knowledge base.
-/

namespace CubeRoot3Irrational

-- The cube root of 3
noncomputable def cbrt3 : ℝ := (3 : ℝ) ^ (1/3 : ℝ)

-- Key property: (3^(1/3))^3 = 3
theorem cbrt3_cubed : cbrt3 ^ 3 = 3 := by
  unfold cbrt3
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

-- 3 is not a perfect cube (1³=1 < 3 < 8=2³)
theorem three_not_perfect_cube : ¬ ∃ (n : ℤ), n ^ 3 = 3 := by
  intro ⟨n, hn⟩
  -- Pattern from knowledge base: establish bounds, use nlinarith with n*n*n
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
  -- So n = 1, but 1³ = 1 ≠ 3
  have : n = 1 := by omega
  rw [this] at hn
  norm_num at hn

-- cbrt3 is not an integer
theorem cbrt3_not_int : ¬ ∃ (n : ℤ), cbrt3 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 3 = 3 := by
    have h1 : cbrt3 ^ 3 = 3 := cbrt3_cubed
    rw [hn] at h1
    exact_mod_cast h1
  exact three_not_perfect_cube ⟨n, h⟩

-- Main theorem: ∛3 is irrational
theorem irrational_cbrt3 : Irrational cbrt3 := by
  apply irrational_nrt_of_notint_nrt 3 3
  · exact_mod_cast cbrt3_cubed
  · exact cbrt3_not_int
  · norm_num

-- Alternative form
theorem irrational_three_pow_one_third : Irrational ((3 : ℝ) ^ (1/3 : ℝ)) :=
  irrational_cbrt3

end CubeRoot3Irrational
