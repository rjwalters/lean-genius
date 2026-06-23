import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-
# Closed form for the arithmetico-geometric sum `∑ k·rᵏ`

## What This Proves

For a field element `r ≠ 1` and a natural number `n`,

    ∑_{k=0}^{n-1} k · rᵏ  =  (r − n·rⁿ + (n−1)·rⁿ⁺¹) / (r − 1)²    (the `(n−1)` is `(n:K) − 1`).

This is the finite **arithmetico-geometric** sum: each term is an arithmetic
factor `k` times a geometric factor `rᵏ`.  It is the discrete analogue of
differentiating the geometric series, and it is exactly the partial sum whose
`n → ∞` limit (for `|r| < 1`) is the well-known `∑ k·rᵏ = r/(1−r)²`.

## Why It Is Not Already in the Gallery / Mathlib

Mathlib has the geometric closed form `geom_sum_eq : ∑ i ∈ range n, xⁱ = (xⁿ−1)/(x−1)`
and the triangular number `Finset.sum_range_id`, but **no closed form for the
weighted sum `∑ k·rᵏ`**.  The gallery's `GeometricSeriesOQ06` is the *infinite*
`tsum k·rᵏ = r/(1−r)²` over a normed field — a different object (a limit, with
`‖r‖ < 1`).  The statement here is the exact finite identity over any field,
valid for every `r ≠ 1` with no analytic hypotheses.

## Method

Induction on `n`.  The inductive step adds the term `m·rᵐ` (from
`Finset.sum_range_succ`) to the closed form at `m`; clearing the common
denominator `(r−1)²` reduces the goal to a polynomial identity closed by `ring`.
The algebra is exactly

    n·rⁿ·(r−1)² = n·rⁿ⁺² − 2n·rⁿ⁺¹ + n·rⁿ,

which absorbs the `−n·rⁿ` and `(n−1)·rⁿ⁺¹` correction terms into the next
closed form.  The companion theorem `sum_range_mul_geom_eq_byParts` records that
the same identity arises from **Abel's summation by parts**
(`Finset.sum_range_by_parts`): with the arithmetic weight `f k = k` the forward
differences `f(k+1) − f k = 1` are constant, so the correction term collapses to
a single nested geometric sum.
-/

namespace SummationByPartsOQ01

open Finset

variable {K : Type*} [Field K]

/-- **Arithmetico-geometric sum, closed form.**
For `r ≠ 1` in a field,
`∑_{k<n} k·rᵏ = (r − n·rⁿ + (n−1)·rⁿ⁺¹)/(r−1)²`. -/
theorem sum_range_mul_geom {r : K} (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (k : K) * r ^ k
      = (r - n * r ^ n + (n - 1) * r ^ (n + 1)) / (r - 1) ^ 2 := by
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

/-- The same closed form, re-derived through **Abel's summation by parts**.
Taking the arithmetic weight `f k = (k : K)` and the geometric sequence
`g k = rᵏ`, `Finset.sum_range_by_parts` rewrites the weighted sum as a boundary
term minus a correction whose increments `f(k+1) − f k = 1` are constant; the
correction is therefore a sum of geometric partial sums. -/
theorem sum_range_mul_geom_eq_byParts (r : K) (n : ℕ) :
    ∑ k ∈ range n, (k : K) * r ^ k
      = (↑(n - 1) : K) * (∑ i ∈ range n, r ^ i)
        - ∑ i ∈ range (n - 1), (∑ j ∈ range (i + 1), r ^ j) := by
  have h := Finset.sum_range_by_parts (fun k => (k : K)) (fun k => r ^ k) n
  simp only [smul_eq_mul] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

end SummationByPartsOQ01
