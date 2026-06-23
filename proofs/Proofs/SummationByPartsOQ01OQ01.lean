import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic

/-
# Closed form for the second-order arithmetico-geometric sum `∑ k²·rᵏ`

## What This Proves

For a field element `r ≠ 1` and a natural number `n`,

    ∑_{k=0}^{n-1} k² · rᵏ
      = (n²·rⁿ − (2n²−2n−1)·rⁿ⁺¹ + (n−1)²·rⁿ⁺² − r² − r) / (r − 1)³

(the natural-number coefficients are read in `K`).  This is the **second-order**
arithmetico-geometric sum: each term carries the quadratic arithmetic weight `k²`
times the geometric factor `rᵏ`.  It is the next step beyond the parent entry
`SummationByPartsOQ01`, which gives the first-order sum `∑ k·rᵏ`, and it is the
finite, hypothesis-free analogue of the twice-differentiated geometric series
whose `n → ∞` limit (for `|r| < 1`) is the classical `∑ k²·rᵏ = r(1+r)/(1−r)³`.

## Why It Is Not Already in the Gallery / Mathlib

Mathlib has `geom_sum_eq` (the geometric closed form) and, via the parent entry,
the gallery now records the first-order `∑ k·rᵏ`.  Neither Mathlib nor the
gallery contains a closed form for the **quadratically weighted** sum `∑ k²·rᵏ`
over a general field.  The infinite gallery entries (`GeometricSeriesOQ06`) are
analytic limits with `‖r‖ < 1`; the identity here is the exact finite sum over
any field with the single algebraic hypothesis `r ≠ 1`.

## Method

`sum_range_sq_mul_geom` is proved by induction on `n`: the inductive step adds
`m²·rᵐ` (via `Finset.sum_range_succ`) to the closed form at `m`; clearing the
common denominator `(r−1)³` reduces the goal to a polynomial identity closed by
`ring`.

`sum_range_sq_mul_geom_eq_byParts` re-derives the same sum through **Abel's
summation by parts** (`Finset.sum_range_by_parts`).  Unlike the first-order case,
the quadratic weight `f k = k²` has *non-constant* forward differences
`f(k+1) − f k = 2k+1`, so summation by parts reduces the second-order sum to a
genuinely first-order weighted sum of geometric partial sums — exhibiting the
recursive ladder `∑ k²·rᵏ ↝ ∑ (2k+1)·(geom) ↝ …`.

`sum_range_sq_mul_geom_two` specializes to `r = 2`, where the cube `(r−1)³ = 1`
collapses the closed form to the clean integer-coefficient identity
`∑_{k<n} k²·2ᵏ = 2ⁿ·(n²−4n+6) − 6`.
-/

namespace SummationByPartsOQ01OQ01

open Finset

variable {K : Type*} [Field K]

/-- **Second-order arithmetico-geometric sum, closed form.**
For `r ≠ 1` in a field,
`∑_{k<n} k²·rᵏ = (n²·rⁿ − (2n²−2n−1)·rⁿ⁺¹ + (n−1)²·rⁿ⁺² − r² − r)/(r−1)³`. -/
theorem sum_range_sq_mul_geom {r : K} (hr : r ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * r ^ k
      = ((n : K) ^ 2 * r ^ n - (2 * n ^ 2 - 2 * n - 1) * r ^ (n + 1)
          + ((n : K) - 1) ^ 2 * r ^ (n + 2) - r ^ 2 - r) / (r - 1) ^ 3 := by
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      field_simp
      ring

/-- The same second-order sum, re-derived through **Abel's summation by parts**.
Taking the quadratic weight `f k = (k : K)²` and the geometric sequence
`g k = rᵏ`, `Finset.sum_range_by_parts` rewrites the weighted sum as a boundary
term minus a correction term.  Here the forward differences
`f(k+1) − f k = 2k+1` are *not* constant, so summation by parts reduces the
second-order sum to a first-order weighted sum of geometric partial sums. -/
theorem sum_range_sq_mul_geom_eq_byParts (r : K) (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * r ^ k
      = (↑(n - 1) : K) ^ 2 * (∑ i ∈ range n, r ^ i)
        - ∑ i ∈ range (n - 1), (2 * (i : K) + 1) * (∑ j ∈ range (i + 1), r ^ j) := by
  have h := Finset.sum_range_by_parts (fun k => (k : K) ^ 2) (fun k => r ^ k) n
  simp only [smul_eq_mul] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

/-- **Concrete specialization at `r = 2`.**
`∑_{k<n} k²·2ᵏ = 2ⁿ·(n²−4n+6) − 6`.  Direct induction (no division), since at
`r = 2` the denominator `(r−1)³ = 1`. -/
theorem sum_range_sq_mul_geom_two (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * 2 ^ k
      = 2 ^ n * ((n : K) ^ 2 - 4 * n + 6) - 6 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

end SummationByPartsOQ01OQ01
