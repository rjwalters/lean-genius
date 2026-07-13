/-
# Irrationality of √2 + √3

## Strategy
1. Assume √2 + √3 = r (rational)
2. Square: (√2 + √3)² = 5 + 2√6 = r²
3. Rearrange: √6 = (r² - 5) / 2
4. But (r² - 5)/2 is rational, contradicting √6 irrational
-/

import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open Real

namespace Sqrt2PlusSqrt3Irrational

/-- √6 is irrational (6 is not a perfect square) -/
theorem irrational_sqrt_six : Irrational (sqrt 6) := by
  have hns : ¬ IsSquare (6 : ℕ) := by native_decide
  exact irrational_sqrt_natCast_iff.mpr hns

/-- Key algebraic identity: (√2 + √3)² = 5 + 2√6 -/
theorem sqrt2_plus_sqrt3_sq :
    (sqrt 2 + sqrt 3) ^ 2 = 5 + 2 * sqrt 6 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have h6 : sqrt 2 * sqrt 3 = sqrt 6 := by
    rw [← sqrt_mul h2 3]
    norm_num
  ring_nf
  rw [sq_sqrt h2, sq_sqrt h3, h6]
  ring

/-- Main theorem: √2 + √3 is irrational -/
theorem irrational_sqrt2_plus_sqrt3 : Irrational (sqrt 2 + sqrt 3) := by
  -- Proof by contradiction: assume √2 + √3 is rational
  intro ⟨r, hr⟩
  -- We have hr : (r : ℝ) = √2 + √3
  -- Squaring gives: r² = (√2 + √3)² = 5 + 2√6
  have hsq : (r : ℝ) ^ 2 = 5 + 2 * sqrt 6 := by
    rw [hr, sqrt2_plus_sqrt3_sq]
  -- Rearranging: √6 = (r² - 5) / 2
  have h6 : sqrt 6 = ((r : ℝ) ^ 2 - 5) / 2 := by linarith
  -- The RHS is rational since r is rational
  have hrat : ∃ q : ℚ, (q : ℝ) = sqrt 6 := by
    use (r ^ 2 - 5) / 2
    simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast]
    exact h6.symm
  -- But √6 is irrational, contradiction
  exact irrational_sqrt_six hrat

end Sqrt2PlusSqrt3Irrational
