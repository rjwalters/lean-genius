import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# The Arithmetico-Geometric Series ∑ n·rⁿ = r/(1−r)² (geometric-series-oq-06)

Differentiating the geometric series `∑ rⁿ = 1/(1 − r)` term by term gives the
**arithmetico-geometric series**

    ∑' n, n · rⁿ = r / (1 − r)²      (‖r‖ < 1).

This is the first moment of the geometric distribution: with success probability
`p = 1 − r`, the expected number of trials is `∑ n·rⁿ⁻¹·p = 1/p`, and the bare
weighted sum `∑ n·rⁿ` is exactly `r/(1 − r)²`.  It is the prototype of every
"weighted geometric" sum appearing in generating-function calculus, queueing
theory, and the analysis of expected running times.

This file packages the identity over a normed field, together with its `HasSum`
and `Summable` forms, the general normed-ring version (using `Ring.inverse`), the
shifted companion `∑ (n+1)·rⁿ = 1/(1 − r)²`, and a concrete evaluation
`∑ n·(1/2)ⁿ = 2`.

Each statement is a thin, named wrapper around Mathlib's
`hasSum_coe_mul_geometric_of_norm_lt_one` / `tsum_coe_mul_geometric_of_norm_lt_one`
(and the `'` ring variants); the shifted companion is a genuine derivation
combining the weighted sum with the plain geometric series.

Status: 0 axioms, 0 sorries
-/

namespace GeometricSeriesOQ06

open scoped Topology

-- ============================================================================
-- Part I: The arithmetico-geometric series over a normed field
-- ============================================================================

variable {𝕜 : Type*} [NormedField 𝕜]

/-- **Arithmetico-geometric series, `HasSum` form.** For `‖r‖ < 1` the partial
sums of `n · rⁿ` converge to `r / (1 − r)²`. -/
theorem hasSum_coe_mul_geometric {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => (n : 𝕜) * r ^ n) (r / (1 - r) ^ 2) :=
  hasSum_coe_mul_geometric_of_norm_lt_one hr

/-- The weighted geometric series `∑ n·rⁿ` is summable when `‖r‖ < 1`. -/
theorem summable_coe_mul_geometric {r : 𝕜} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => (n : 𝕜) * r ^ n) :=
  (hasSum_coe_mul_geometric hr).summable

/-- **Arithmetico-geometric series.** For `‖r‖ < 1`,

    ∑' n, n · rⁿ = r / (1 − r)². -/
theorem tsum_coe_mul_geometric {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : 𝕜) * r ^ n = r / (1 - r) ^ 2 :=
  tsum_coe_mul_geometric_of_norm_lt_one hr

-- ============================================================================
-- Part II: The shifted companion ∑ (n+1)·rⁿ = 1/(1 − r)²
-- ============================================================================

/-- **Shifted arithmetico-geometric series.** Adding the plain geometric series
`∑ rⁿ = (1 − r)⁻¹` to `∑ n·rⁿ = r/(1 − r)²` shifts the index:

    ∑' n, (n + 1) · rⁿ = (1 − r)⁻² .

This is the second derivative form `d²/dr² ∑ rⁿ`-style identity that underlies the
negative-binomial generating function. -/
theorem tsum_succ_mul_geometric {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, ((n : 𝕜) + 1) * r ^ n = (1 - r)⁻¹ ^ 2 := by
  have hne : (1 : 𝕜) - r ≠ 0 := by
    rcases eq_or_ne r 1 with rfl | hr1
    · simp at hr
    · exact sub_ne_zero.mpr (Ne.symm hr1)
  have hsum := (hasSum_coe_mul_geometric hr).add (hasSum_geometric_of_norm_lt_one hr)
  have hcongr : (fun n : ℕ => (n : 𝕜) * r ^ n + r ^ n)
      = fun n : ℕ => ((n : 𝕜) + 1) * r ^ n := by
    funext n; ring
  rw [hcongr] at hsum
  have hval : r / (1 - r) ^ 2 + (1 - r)⁻¹ = (1 - r)⁻¹ ^ 2 := by
    field_simp
    ring
  rw [hval] at hsum
  exact hsum.tsum_eq

-- ============================================================================
-- Part III: The general normed-ring version (Ring.inverse)
-- ============================================================================

/-- **Arithmetico-geometric series over a normed ring.** In any normed ring with
summable geometric series (e.g. a Banach algebra), for `‖x‖ < 1`,

    ∑' n, n · xⁿ = x · (1 − x)⁻¹ ²,

using `Ring.inverse` in place of field division. -/
theorem tsum_coe_mul_geometric_ring {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {x : R} (hx : ‖x‖ < 1) :
    ∑' n : ℕ, (n : R) * x ^ n = x * Ring.inverse (1 - x) ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one' hx).tsum_eq

-- ============================================================================
-- Part IV: A concrete evaluation
-- ============================================================================

/-- **Concrete value.** Taking `r = 1/2` over `ℝ`:

    ∑' n, n · (1/2)ⁿ = 2.

So the expected number of fair-coin tosses weighted by trial index sums to 2 —
the classic `∑ n/2ⁿ = 2`. -/
theorem tsum_nat_mul_half_pow : ∑' n : ℕ, (n : ℝ) * (1 / 2) ^ n = 2 := by
  have h : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
  rw [tsum_coe_mul_geometric h]
  norm_num

-- ============================================================================
-- Part V: Summary
-- ============================================================================

/-
## Summary

| Result | Statement | Backing |
|--------|-----------|---------|
| `hasSum_coe_mul_geometric` | partial sums → r/(1−r)² | `hasSum_coe_mul_geometric_of_norm_lt_one` |
| `tsum_coe_mul_geometric` | ∑ n·rⁿ = r/(1−r)² | `tsum_coe_mul_geometric_of_norm_lt_one` |
| `summable_coe_mul_geometric` | ∑ n·rⁿ summable | `HasSum.summable` |
| `tsum_succ_mul_geometric` | ∑ (n+1)·rⁿ = (1−r)⁻² | weighted + geometric series |
| `tsum_coe_mul_geometric_ring` | ring version (Ring.inverse) | `…_of_norm_lt_one'` |
| `tsum_nat_mul_half_pow` | ∑ n·(1/2)ⁿ = 2 | specialize at r = 1/2 |

The arithmetico-geometric series is the term-by-term derivative of the geometric
series: from `∑ rⁿ = 1/(1 − r)` one gets `∑ n·rⁿ⁻¹ = 1/(1 − r)²`, i.e.
`∑ n·rⁿ = r/(1 − r)²`.  Specializing to `r = 1/2` recovers the textbook
`∑ n/2ⁿ = 2`, the first moment of the geometric distribution.
-/

end GeometricSeriesOQ06

#check @GeometricSeriesOQ06.tsum_coe_mul_geometric
#check @GeometricSeriesOQ06.tsum_succ_mul_geometric
#check @GeometricSeriesOQ06.tsum_coe_mul_geometric_ring
#check @GeometricSeriesOQ06.tsum_nat_mul_half_pow
