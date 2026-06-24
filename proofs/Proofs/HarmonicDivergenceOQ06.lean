/-
  Divergence of reciprocals along an arithmetic progression
  Open Question: harmonic-divergence-oq-06

  The series of reciprocals of the odd numbers, Σ 1/(2n+1), diverges. We prove
  this as a corollary of a general statement: for any real a > 0 and b > 0, the
  series Σ 1/(a·n + b) of reciprocals along the arithmetic progression
  a·n + b is not summable.

  ## Main Result

  `not_summable_one_div_arith` (PROVED): for a > 0, b > 0,
    ¬ Summable (fun n : ℕ => 1 / (a * n + b))

  ## Corollaries

  `not_summable_one_div_odd`  : ¬ Summable (fun n => 1 / (2n + 1))   (odd reciprocals)
  `not_summable_one_div_even` : ¬ Summable (fun n => 1 / (2n + 2))   (even reciprocals)
  `tendsto_sum_one_div_odd_atTop` : the partial sums Σ_{i<n} 1/(2i+1) → ∞.

  ## Proof Strategy

  Compare against the (shifted) harmonic series. For a > 0, b > 0 and every n,
    a·n + b ≤ (a + b)·(n + 1),
  hence
    1/(n+1) ≤ (a + b) · 1/(a·n + b).
  If Σ 1/(a·n + b) were summable, so would be (a+b)·Σ 1/(a·n+b), and by the
  comparison test Σ 1/(n+1) would be summable — contradicting the divergence of
  the harmonic series (`Real.not_summable_one_div_natCast`, transported across
  the index shift by `summable_nat_add_iff`).
-/

import Mathlib

open Filter Topology

namespace HarmonicDivergenceOQ06

/-- **Main result.** For real `a > 0` and `b > 0`, the series of reciprocals
    along the arithmetic progression `a·n + b` diverges: it is not summable.

    Proof by comparison with the harmonic series, using
    `a·n + b ≤ (a + b)·(n + 1)`, i.e. `1/(n+1) ≤ (a+b)·1/(a·n+b)`. -/
theorem not_summable_one_div_arith (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ¬ Summable (fun n : ℕ => 1 / (a * n + b)) := by
  intro hsum
  -- Scaling a summable series keeps it summable.
  have hscaled : Summable (fun n : ℕ => (a + b) * (1 / (a * (n : ℝ) + b))) :=
    hsum.mul_left (a + b)
  -- The shifted harmonic series is dominated by the scaled series, hence summable.
  have hcomp : Summable (fun n : ℕ => 1 / ((↑(n + 1)) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hscaled
    -- Goal: 1/(n+1) ≤ (a+b) * (1/(a*n+b))
    rw [mul_one_div, le_div_iff₀ (show (0:ℝ) < a * ↑n + b by positivity),
      div_mul_eq_mul_div, div_le_iff₀ (show (0:ℝ) < ((↑(n + 1)) : ℝ) by positivity)]
    -- Goal: 1 * (a*n+b) ≤ (a+b) * (n+1)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n, ha.le, hb.le]
  -- But the shifted harmonic series is not summable.
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp hcomp)

/-- The reciprocals of the odd numbers diverge: `¬ Summable (fun n => 1/(2n+1))`.
    This is the headline statement of the open question (a = 2, b = 1). -/
theorem not_summable_one_div_odd :
    ¬ Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 1)) :=
  not_summable_one_div_arith 2 1 (by norm_num) (by norm_num)

/-- The reciprocals of the positive even numbers diverge:
    `¬ Summable (fun n => 1/(2n+2))` (a = 2, b = 2). Together with the odd case
    this exhibits the harmonic series as the union of two divergent halves. -/
theorem not_summable_one_div_even :
    ¬ Summable (fun n : ℕ => 1 / (2 * (n : ℝ) + 2)) :=
  not_summable_one_div_arith 2 2 (by norm_num) (by norm_num)

/-- The partial sums of the odd-reciprocal series tend to infinity:
    `∑_{i < n} 1/(2i+1) → ∞`. The explicit divergence statement equivalent to
    non-summability, since the terms are nonnegative. -/
theorem tendsto_sum_one_div_odd_atTop :
    Tendsto (fun n => ∑ i ∈ Finset.range n, 1 / (2 * (i : ℝ) + 1)) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg (fun i => by positivity)]
  exact not_summable_one_div_odd

end HarmonicDivergenceOQ06
