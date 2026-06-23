/-
# The p-series convergence test

The *p-series* is the real-valued series

  ∑' n : ℕ, 1 / nᵖ

This file packages the classical convergence dichotomy: the p-series converges
**if and only if** `1 < p`. In particular the harmonic series (`p = 1`) diverges,
sitting exactly on the boundary, while every exponent strictly above `1`
(such as the Basel exponent `p = 2`) converges.

The general real-exponent threshold is the headline statement; we state it for a
real exponent `p` (using `Real.rpow`), specialise it to a natural-number exponent
and to the two-sided `ℤ`-indexed series, and record the boundary case `p = 1`
(the harmonic series) as a divergence corollary.

## Main results

* `pSeries_summable_iff_one_lt` : `Summable (fun n => 1 / (n : ℝ) ^ p) ↔ 1 < p`
  for a real exponent `p` (rpow form, the sharp threshold).
* `pSeries_nat_summable_iff_one_lt` : the same for a natural-number exponent.
* `pSeries_int_summable_iff_one_lt` : the two-sided `ℤ`-indexed version.
* `harmonic_not_summable` : the harmonic series (`p = 1`) diverges.
* `pSeries_summable_of_one_lt` / `pSeries_basel_summable` : convergence for
  `1 < p` and the Basel exponent `p = 2`.

All proofs reduce to the Mathlib `p`-series engine
(`Real.summable_one_div_nat_rpow` and friends) and are fully machine-checked with
no additional axioms.
-/

import Mathlib

namespace PSeriesConvergenceOQ01

open scoped Real

/-- **p-series test (real exponent).** The real-valued series `∑' n, 1 / nᵖ`,
with `nᵖ` the real power `Real.rpow`, converges **iff** `1 < p`. This is the sharp
convergence threshold for the p-series. -/
theorem pSeries_summable_iff_one_lt {p : ℝ} :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
  Real.summable_one_div_nat_rpow

/-- **p-series test (natural exponent).** For a natural-number exponent the series
`∑' n, 1 / nᵖ` (ordinary monoid power) converges **iff** `1 < p`. -/
theorem pSeries_nat_summable_iff_one_lt {p : ℕ} :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
  Real.summable_one_div_nat_pow

/-- **p-series test (two-sided `ℤ`).** The series summed over all integers,
`∑' n : ℤ, 1 / nᵖ`, converges **iff** `1 < p`. -/
theorem pSeries_int_summable_iff_one_lt {p : ℕ} :
    Summable (fun n : ℤ => 1 / (n : ℝ) ^ p) ↔ 1 < p :=
  Real.summable_one_div_int_pow

/-- **Convergence half** for any real exponent above the threshold: `1 < p`
implies the p-series converges. -/
theorem pSeries_summable_of_one_lt {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) :=
  pSeries_summable_iff_one_lt.mpr hp

/-- **The harmonic series diverges.** This is the boundary case `p = 1` of the
test: `∑' n, 1 / n` is *not* summable, so `1 < p` cannot be relaxed to `1 ≤ p`. -/
theorem harmonic_not_summable :
    ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) := by
  simpa using Real.not_summable_one_div_natCast

/-- The harmonic series sits exactly on the boundary: it is the `p = 1`
instance, where the strict inequality `1 < p` fails. -/
theorem harmonic_eq_pSeries_one :
    (fun n : ℕ => 1 / (n : ℝ)) = (fun n : ℕ => 1 / (n : ℝ) ^ (1 : ℕ)) := by
  simp

/-- **Basel exponent.** The exponent `p = 2` lies above the threshold, so the
series `∑' n, 1 / n²` converges. -/
theorem pSeries_basel_summable :
    Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
  pSeries_nat_summable_iff_one_lt.mpr (by norm_num)

end PSeriesConvergenceOQ01
