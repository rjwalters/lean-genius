/-
  Aristotle targets for Erdős Problem #1002 OQ-01-OQ-01: Weyl Equidistribution
  Routine supporting lemmas for automated proof search.
  See Erdos1002OQ01OQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjecture or the deep axiom (innerSum_log_bound)
  - Routine properties of deviation, innerSum, and Int.fract
  - Clean theorem statements with no definition sorries
  - No axioms

  These lemmas support a future proof of weyl_fract_average_zero.

  Sorries targeted:
  - deviation_bounded: |1/2 - {x}| ≤ 1/2
    Strategy: Int.fract_nonneg + Int.fract_lt_one + abs_le
  - deviation_periodic: deviation(x+1) = deviation(x)
    Strategy: Int.fract_add_int or Int.fract_int_add
  - innerSum_eq_sub_fract: innerSum α n = n/2 - Σ{α(k+1)}
    Strategy: unfold, Finset.sum_sub_distrib, Finset.sum_const
  - innerSum_abs_le: |innerSum α n| ≤ n/2
    Strategy: abs of sum ≤ sum of abs, then deviation_bounded
  - deviation_integral_zero: ∫₀¹ (1/2 - {x}) dx = 0
    Strategy: Int.fract_eq_self on (0,1), then ∫₀¹ x dx = 1/2
-/
import Mathlib

open Real Filter Finset

namespace Erdos1002OQ01OQ01Aristotle

/-- Deviation from midpoint: 1/2 - {x}. Same as main file. -/
noncomputable def deviation (x : ℝ) : ℝ := 1 / 2 - Int.fract x

/-- Inner sum: S(α, n) = Σ_{k=1}^n (1/2 - {αk}). Same as main file. -/
noncomputable def innerSum (α : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, deviation (α * (↑k + 1))

/-- Routine: deviation is bounded by 1/2.
    Since 0 ≤ Int.fract x < 1, we have -1/2 < 1/2 - Int.fract x ≤ 1/2.
    Strategy: use Int.fract_nonneg, Int.fract_lt_one, abs_le. -/
theorem deviation_bounded (x : ℝ) : |deviation x| ≤ 1 / 2 := by
  sorry

/-- Routine: deviation has period 1.
    Strategy: Int.fract_add_int x 1 gives Int.fract(x + 1) = Int.fract x. -/
theorem deviation_periodic (x : ℝ) : deviation (x + 1) = deviation x := by
  sorry

/-- Routine: innerSum rewrites as n/2 minus sum of fractional parts.
    Strategy: unfold deviation in sum, split Σ(a - b) = Σa - Σb, Σ(1/2) = n/2. -/
theorem innerSum_eq_sub_fract (α : ℝ) (n : ℕ) :
    innerSum α n = ↑n / 2 - ∑ k ∈ range n, Int.fract (α * (↑k + 1)) := by
  sorry

/-- Routine: innerSum at 0 is zero.
    Strategy: simp with sum_range_zero or sum_empty. -/
theorem innerSum_zero (α : ℝ) : innerSum α 0 = 0 := by
  sorry

/-- Routine: |innerSum α n| ≤ n/2.
    Strategy: Finset.abs_sum_le_sum_abs + deviation_bounded. -/
theorem innerSum_abs_le (α : ℝ) (n : ℕ) : |innerSum α n| ≤ ↑n / 2 := by
  sorry

/-- Routine: the integral of deviation over [0,1] is zero.
    On (0,1), Int.fract x = x, so ∫₀¹ deviation x dx = ∫₀¹ (1/2 - x) dx = 1/2 - 1/2 = 0.
    Strategy: rewrite Int.fract to x on (0,1) ae, integrate. -/
theorem deviation_integral_zero :
    ∫ x in (0 : ℝ)..1, (1 / 2 - Int.fract x) = 0 := by
  sorry

end Erdos1002OQ01OQ01Aristotle
