/-
Proof: Irrationality of ∜2
Generated: 2025-12-31
Pattern: nrt-irrational
Method: Template-based derivation
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Irrationality of ∜2

## Strategy
If x^n = m (integer) and x is not an integer, then x is irrational.

For ∜2: x = 2^(1/4), n = 4, m = 2
- (2^(1/4))^4 = 2
- 2 is not a perfect four power (1^4=1 < 2 < 16=2^4)
- Therefore 2^(1/4) is not an integer
- Therefore ∜2 is irrational
-/

namespace FourthRoot2Irrational

-- The four root of 2
noncomputable def fourthrt2 : ℝ := (2 : ℝ) ^ (1/4 : ℝ)

-- Key property: (2^(1/4))^4 = 2
theorem fourthrt2_pow : fourthrt2 ^ 4 = 2 := by
  unfold fourthrt2
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

-- 2 is not a perfect four power
theorem two_not_perfect_four_power : ¬ ∃ (n : ℤ), n ^ 4 = 2 := by
  intro ⟨n, hn⟩
  have h1 : 0 < n := by
    by_contra h
    push_neg at h
    have hn_pow : n ^ 4 ≤ 0 := by
      have : n ^ 4 = n * n * n * n := by ring
      rw [this]
      nlinarith
    omega
  have h2 : n < 2 := by
    by_contra h
    push_neg at h
    have hn_pow : n ^ 4 ≥ 16 := by
      have : n ^ 4 = n * n * n * n := by ring
      rw [this]
      nlinarith
    omega
  -- Eliminate remaining candidates (n ∈ {1..2-1}, none are 4-th powers of 2)
  interval_cases n
  all_goals norm_num at hn

-- fourthrt2 is not an integer
theorem fourthrt2_not_int : ¬ ∃ (n : ℤ), fourthrt2 = n := by
  intro ⟨n, hn⟩
  have h : n ^ 4 = 2 := by
    have h1 : fourthrt2 ^ 4 = 2 := fourthrt2_pow
    rw [hn] at h1
    exact_mod_cast h1
  exact two_not_perfect_four_power ⟨n, h⟩

-- Main theorem: ∜2 is irrational
theorem irrational_fourthrt2 : Irrational fourthrt2 := by
  apply irrational_nrt_of_notint_nrt 4 2
  · exact_mod_cast fourthrt2_pow
  · exact fourthrt2_not_int
  · norm_num

-- Alternative form
theorem irrational_2_pow_one_four : Irrational ((2 : ℝ) ^ (1/4 : ℝ)) :=
  irrational_fourthrt2

end FourthRoot2Irrational
