import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Analysis.SpecificLimits.Normed
import Proofs.DerangementsConvergenceOQ05
import Mathlib.Tactic

/-
# A Sharp Factorial-Rate Bound for the Fixed-Point Distribution

This file answers the open question recorded with `derangements-convergence-oq-05`:

> The parent entry proves the *pointwise* Poisson(1) limit
> `D_k(n)/n! → e⁻¹/k!`.  At what **rate** does it converge?

We give the explicit, non-asymptotic error bound, valid for every `k ≤ n`:

  `| D_k(n)/n!  −  e⁻¹/k! |  ≤  1 / (k! · (n−k+1)!)`.

This is the *sharp* alternating-series bound: the per-`k` Poisson error decays
like one over a factorial, faster than any power of `n` for fixed `k`.

## Strategy

Writing `m = n − k`, the parent's `fixedPointProb_eq` gives
`D_k(n)/n! = (1/k!) · (D(m)/m!)`, where `D = numDerangements`.  The key arithmetic
identity (extracted from the internals of Mathlib's `numDerangements_tendsto_inv_e`)
is that `D(m)/m!` is exactly the `(m+1)`-term partial sum of the series for `e⁻¹`:

  `D(m)/m! = ∑_{j=0}^{m} (−1)ʲ / j!`.

Since `e⁻¹ = ∑_{j} (−1)ʲ/j!` with `1/j!` antitone and summable, Mathlib's
`alternating_series_error_bound` bounds the tail by the first omitted term:

  `| e⁻¹ − ∑_{j=0}^{m} (−1)ʲ/j! | ≤ 1/(m+1)!`.

Dividing by `k!` gives the claimed bound.  No `e⁻¹` series machinery is rebuilt:
the convergence of `∑ xⁿ/n!` to `exp x` comes from `expSeries_div_hasSum_exp`.

## Main results

* `numDerangements_div_factorial` : `D(m)/m! = ∑_{j≤m} (−1)ʲ/j!`.
* `expNegOne_sub_partialSum_le` : `|e⁻¹ − ∑_{j≤m}(−1)ʲ/j!| ≤ 1/(m+1)!`.
* `fixedPointProb_sub_poisson_le` : the headline `|D_k(n)/n! − e⁻¹/k!| ≤ 1/(k!(n−k+1)!)`.
-/

open Finset Filter Topology NormedSpace

namespace DerangementsFixedPointDistribution

/-- `1/j!` is antitone in `j` (factorials are monotone, reciprocals reverse the order). -/
theorem one_div_factorial_antitone :
    Antitone (fun j : ℕ => (1 : ℝ) / (j.factorial : ℝ)) := by
  intro a b hab
  apply one_div_le_one_div_of_le
  · exact_mod_cast Nat.factorial_pos a
  · exact_mod_cast Nat.factorial_le hab

/-- `∑_j 1/j!` is summable: it is the `x = 1` exponential series. -/
theorem one_div_factorial_summable :
    Summable (fun j : ℕ => (1 : ℝ) / (j.factorial : ℝ)) := by
  have h := expSeries_div_hasSum_exp ℝ (1 : ℝ)
  simp only [one_pow] at h
  exact h.summable

/-- The alternating exponential series at `x = -1` sums to `e⁻¹`. -/
theorem hasSum_expNegOne :
    HasSum (fun j : ℕ => (-1 : ℝ) ^ j / (j.factorial : ℝ)) (Real.exp (-1)) := by
  rw [Real.exp_eq_exp_ℝ]
  exact expSeries_div_hasSum_exp ℝ (-1 : ℝ)

/-- **The derangement ratio is a partial sum of `e⁻¹`.**
`numDerangements m / m! = ∑_{j=0}^{m} (-1)ʲ / j!`.  This identity is the arithmetic
core of `numDerangements_tendsto_inv_e`; we isolate it as a standalone lemma. -/
theorem numDerangements_div_factorial (m : ℕ) :
    (numDerangements m : ℝ) / (m.factorial : ℝ)
      = ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ) := by
  rw [← Int.cast_natCast, numDerangements_sum]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have h_le : j ≤ m := Finset.mem_range_succ_iff.mp hj
  rw [Nat.ascFactorial_eq_div, add_tsub_cancel_of_le h_le]
  push_cast [Nat.factorial_dvd_factorial h_le]
  field_simp

/-- **Sharp alternating-series remainder for `e⁻¹`.**
The `(m+1)`-term partial sum approximates `e⁻¹` to within the first omitted term:
`|e⁻¹ − ∑_{j=0}^{m}(-1)ʲ/j!| ≤ 1/(m+1)!`. -/
theorem expNegOne_sub_partialSum_le (m : ℕ) :
    |Real.exp (-1) - ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)|
      ≤ 1 / ((m + 1).factorial : ℝ) := by
  have herr := alternating_series_error_bound
    (fun j : ℕ => (1 : ℝ) / (j.factorial : ℝ))
    one_div_factorial_antitone one_div_factorial_summable (m + 1)
  simp only [mul_one_div] at herr
  rwa [hasSum_expNegOne.tsum_eq] at herr

/-- **Quantitative Poisson(1) rate for the fixed-point distribution.**

For every `k ≤ n`, the probability `D_k(n)/n!` that a uniform random permutation of
`Fin n` has exactly `k` fixed points differs from its Poisson(1) limit `e⁻¹/k!` by at
most `1/(k!·(n−k+1)!)`:

  `| D_k(n)/n! − e⁻¹/k! | ≤ 1 / (k! · (n−k+1)!)`.

The bound is explicit (no hidden constants) and decays faster than any power of `n`
for fixed `k`, giving the `O(1/n!)` rate the parent's open question anticipated. -/
theorem fixedPointProb_sub_poisson_le (n k : ℕ) (h : k ≤ n) :
    |fixedPointProb n k - Real.exp (-1) / (k.factorial : ℝ)|
      ≤ 1 / ((k.factorial : ℝ) * ((n - k + 1).factorial : ℝ)) := by
  set m := n - k with hm
  have hk0 : (0 : ℝ) ≤ 1 / (k.factorial : ℝ) := by positivity
  rw [fixedPointProb_eq n k h, numDerangements_div_factorial m]
  have hrw :
      (1 / (k.factorial : ℝ)) * (∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ))
          - Real.exp (-1) / (k.factorial : ℝ)
        = (1 / (k.factorial : ℝ))
            * ((∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)) - Real.exp (-1)) := by
    ring
  rw [hrw, abs_mul, abs_of_nonneg hk0, abs_sub_comm]
  calc
    (1 / (k.factorial : ℝ))
        * |Real.exp (-1) - ∑ j ∈ Finset.range (m + 1), (-1 : ℝ) ^ j / (j.factorial : ℝ)|
        ≤ (1 / (k.factorial : ℝ)) * (1 / ((m + 1).factorial : ℝ)) :=
          mul_le_mul_of_nonneg_left (expNegOne_sub_partialSum_le m) hk0
    _ = 1 / ((k.factorial : ℝ) * ((m + 1).factorial : ℝ)) := by
          rw [div_mul_div_comm, mul_one]

end DerangementsFixedPointDistribution
