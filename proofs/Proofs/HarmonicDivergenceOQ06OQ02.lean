/-
  Divergence of Σ 1/(a·n + b) for a > 0, b ≥ 0 — the b = 0 endpoint
  Open Question: harmonic-divergence-oq-06-oq-02

  The parent `harmonic-divergence-oq-06` proves, for real a > 0 and *b > 0*,
  that Σ 1/(a·n + b) diverges (comparison with the shifted harmonic series via
  a·n + b ≤ (a + b)·(n + 1)). That comparison genuinely needs b > 0: at n = 0
  with b = 0 the term 1/(a·0 + 0) = 1/0 is 0 by Lean's junk-value convention, so
  the pointwise bound 1/(n+1) ≤ (a+b)·1/(a·n+b) fails (1 ≤ 0).

  This entry closes the last gap, b = 0. When b = 0 the series is the harmonic
  series rescaled by 1/a:

      Σ_{n ≥ 1} 1/(a·n) = (1/a) · Σ_{n ≥ 1} 1/n = +∞.

  The n = 0 term is excised by an index shift; the rest factors as (1/a)·(1/n)
  and reduces to `Real.not_summable_one_div_natCast`.

  ## Main results

  `not_summable_one_div_scaled` (a > 0):
      ¬ Summable (fun n => 1 / (a · n))                    -- the b = 0 core

  `not_summable_one_div_arith'` (a > 0, 0 ≤ b):
      ¬ Summable (fun n => 1 / (a · n + b))                -- unified b ≥ 0 statement

  ## Corollaries

  `not_summable_one_div_multiples`      : reciprocals of positive multiples of a
  `not_summable_harmonic`               : a = 1, b = 0 recovers the raw harmonic series
  `tendsto_sum_one_div_scaled_atTop`    : partial sums of Σ 1/(a·(n+1)) → ∞
-/

import Mathlib
import Proofs.HarmonicDivergenceOQ06

open Filter Topology

namespace HarmonicDivergenceOQ06OQ02

/-- **Scaled-harmonic divergence (the b = 0 endpoint).** For real `a > 0`, the
    reciprocals of the multiples of `a` are not summable:
    `¬ Summable (fun n => 1 / (a · n))`.

    The `n = 0` term is `1/0 = 0`; discarding it via an index shift leaves
    `(1/a)·Σ 1/(n+1)`, which diverges because the harmonic series does. -/
theorem not_summable_one_div_scaled (a : ℝ) (ha : 0 < a) :
    ¬ Summable (fun n : ℕ => 1 / (a * (n : ℝ))) := by
  intro hsum
  have hane : a ≠ 0 := ha.ne'
  -- Discard the n = 0 term (`1/0 = 0`) by shifting the index up by one.
  have hsum1 : Summable (fun n : ℕ => 1 / (a * ((n : ℝ) + 1))) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (a * (n : ℝ))) 1).mpr hsum
    simpa using h
  -- Multiply by `a`: the constant multiple reduces to the shifted harmonic series.
  have hharm : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    refine (hsum1.mul_left a).congr (fun n => ?_)
    rw [one_div, mul_inv, ← mul_assoc, mul_inv_cancel₀ hane, one_mul, one_div]
  -- But the shifted harmonic series is not summable.
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp (by simpa using hharm))

/-- **Unified arithmetic-progression divergence, `b ≥ 0`.** For real `a > 0` and
    `b ≥ 0`, the reciprocals along `a·n + b` are not summable. This subsumes the
    parent (`b > 0`) and the scaled-harmonic endpoint (`b = 0`) in one statement. -/
theorem not_summable_one_div_arith' (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ¬ Summable (fun n : ℕ => 1 / (a * n + b)) := by
  rcases hb.lt_or_eq with hpos | hzero
  · -- b > 0 : this is exactly the parent theorem.
    exact HarmonicDivergenceOQ06.not_summable_one_div_arith a b ha hpos
  · -- b = 0 : the series is `1/(a·n)`, handled by the scaled-harmonic lemma.
    subst hzero
    simpa using not_summable_one_div_scaled a ha

/-- Reciprocals of the positive multiples of `a` diverge (index shifted so the
    first term is `1/a`): `¬ Summable (fun n => 1 / (a·(n+1)))`. -/
theorem not_summable_one_div_multiples (a : ℝ) (ha : 0 < a) :
    ¬ Summable (fun n : ℕ => 1 / (a * ((n : ℝ) + 1))) := by
  intro hsum
  exact not_summable_one_div_scaled a ha
    ((summable_nat_add_iff (f := fun n : ℕ => 1 / (a * (n : ℝ))) 1).mp (by simpa using hsum))

/-- The raw harmonic series is the `a = 1, b = 0` instance. -/
theorem not_summable_harmonic :
    ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) := by
  simpa using not_summable_one_div_scaled 1 (by norm_num)

/-- The partial sums of the scaled-harmonic series `Σ_{i<n} 1/(a·(i+1))` tend to
    `+∞`, the explicit divergence statement (terms are nonnegative). -/
theorem tendsto_sum_one_div_scaled_atTop (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, 1 / (a * ((i : ℝ) + 1))) atTop atTop := by
  rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg (fun i => by positivity)]
  exact not_summable_one_div_multiples a ha

end HarmonicDivergenceOQ06OQ02
