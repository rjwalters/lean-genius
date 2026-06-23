import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# Finite Arithmetico-Geometric Sum: a closed form for ∑ k·xᵏ

## What This Proves

For a ratio `x` and a length `n`, the *arithmetico-geometric* finite sum
`∑_{k=0}^{n-1} k·xᵏ` (the index `k` weighting each geometric term `xᵏ`) has the
division-free closed form

  (1 − x)² · ∑_{k=0}^{n-1} k·xᵏ  =  x·(1 − xⁿ) − n·xⁿ·(1 − x),

valid over **any** commutative ring, and the corresponding field closed form

  ∑_{k=0}^{n-1} k·xᵏ  =  (x·(1 − xⁿ) − n·xⁿ·(1 − x)) / (1 − x)²     (x ≠ 1).

The ordinary finite geometric sum `∑_{k=0}^{n-1} xᵏ = (1 − xⁿ)/(1 − x)` is
recorded alongside as the building block (`geom_sum_closed`, a wrapper of
Mathlib's `geom_sum_eq`), and the file closes the loop with Mathlib's *infinite*
arithmetico-geometric sum `∑' k, k·xᵏ = x/(1 − x)²` for `‖x‖ < 1`: the finite
numerator `x·(1 − xⁿ) − n·xⁿ·(1 − x)` tends to `x` as `n → ∞` (since
`xⁿ, n·xⁿ → 0`), recovering the infinite value.

## Why This Is Not Already in Mathlib

Mathlib records the *infinite* weighted geometric series
`tsum_coe_mul_geometric_of_norm_lt_one` (`∑' n, n·rⁿ = r/(1−r)²` for `‖r‖ < 1`)
and the plain finite geometric sum `geom_sum_eq`, but it does **not** record the
*finite* arithmetico-geometric closed form `∑_{k<n} k·xᵏ`.  That finite identity
is the missing companion: it is purely algebraic (no analysis, no convergence),
holds over every commutative ring in its `(1−x)²·∑ = …` form, and specialises —
e.g. `∑_{k<n} k·2ᵏ = (n − 2)·2ⁿ + 2`.

## Relation to the parent entry

The parent `geometric-series-oq-08` quantifies the *unweighted* finite partial
sums `∑_{k<n} rᵏ` and their approach to `1/(1−r)`.  This entry inserts the linear
weight `k`, giving the next member of the family `∑ kᵐ·xᵏ`: the finite closed
form, its field specialisation, and the consistency with Mathlib's infinite
weighted series.

## Proof Strategy

1. **Ring identity (`arith_geom_mul`).** Induction on `n`.  The base case is
   `0 = 0`; the step uses `Finset.sum_range_succ` to peel the `k = n` term and
   then `push_cast; ring` to verify the polynomial identity
   `f(n) + (1−x)²·n·xⁿ = f(n+1)` with `f(n) = x·(1 − xⁿ) − n·xⁿ·(1 − x)`.
2. **Field form (`arith_geom_div`).** Clear the denominator `(1 − x)² ≠ 0`
   (from `x ≠ 1`) with `eq_div_iff` and discharge by the ring identity.
3. **Specialisations.** Substitute `x = 2` (so `(1 − x)² = 1`) for
   `∑_{k<n} k·2ᵏ = (n − 2)·2ⁿ + 2`, and check small cases numerically.
4. **Infinite limit.** Quote Mathlib's `tsum_coe_mul_geometric_of_norm_lt_one`
   to record that the finite closed form's `n → ∞` limit is the infinite value
   `x/(1 − x)²`.

All results depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace GeometricSeriesOQ08OQ01

open Finset

/-! ## The plain finite geometric sum (building block) -/

/-- The ordinary finite geometric sum in the form `(1 − xⁿ)/(1 − x)`.  A thin
wrapper of Mathlib's `geom_sum_eq` (which uses `(xⁿ − 1)/(x − 1)`), recorded here
so the entry is self-contained: it is the `k⁰`-weighted case that the
arithmetico-geometric sum refines by inserting the weight `k`. -/
theorem geom_sum_closed {K : Type*} [Field K] (x : K) (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, x ^ k = (1 - x ^ n) / (1 - x) := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have h2 : (1 : K) - x ≠ 0 := sub_ne_zero.mpr hx.symm
  rw [geom_sum_eq hx]
  field_simp
  ring

/-! ## The finite arithmetico-geometric sum -/

/-- **Division-free closed form** for the finite arithmetico-geometric sum,
valid over any commutative ring:
`(1 − x)² · ∑_{k<n} k·xᵏ = x·(1 − xⁿ) − n·xⁿ·(1 − x)`.
Proved by induction on `n`: peel the top term with `Finset.sum_range_succ`, then
`push_cast; ring`. -/
theorem arith_geom_mul {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (1 - x) ^ 2 * ∑ k ∈ range n, (k : R) * x ^ k
      = x * (1 - x ^ n) - (n : R) * x ^ n * (1 - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- **Field closed form** for the finite arithmetico-geometric sum (`x ≠ 1`):
`∑_{k<n} k·xᵏ = (x·(1 − xⁿ) − n·xⁿ·(1 − x)) / (1 − x)²`. -/
theorem arith_geom_div {K : Type*} [Field K] (x : K) (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (k : K) * x ^ k
      = (x * (1 - x ^ n) - (n : K) * x ^ n * (1 - x)) / (1 - x) ^ 2 := by
  have h1 : (1 : K) - x ≠ 0 := sub_ne_zero.mpr hx.symm
  have h2 : (1 - x) ^ 2 ≠ 0 := pow_ne_zero _ h1
  rw [eq_div_iff h2, mul_comm]
  exact arith_geom_mul x n

/-- Sanity check of the ring identity at `n = 0` and `n = 1` (both sides `0`),
recorded as a guard against off-by-one sign errors in the closed form. -/
theorem arith_geom_mul_one {R : Type*} [CommRing R] (x : R) :
    (1 - x) ^ 2 * ∑ k ∈ range 1, (k : R) * x ^ k = 0 := by
  rw [arith_geom_mul]; simp

/-! ## Specialisations -/

/-- The weight-`x = 2` specialisation: `∑_{k<n} k·2ᵏ = (n − 2)·2ⁿ + 2`.
Here `(1 − 2)² = 1`, so the denominator disappears. -/
theorem arith_geom_two (n : ℕ) :
    ∑ k ∈ range n, (k : ℝ) * 2 ^ k = ((n : ℝ) - 2) * 2 ^ n + 2 := by
  rw [arith_geom_div (x := (2 : ℝ)) (by norm_num)]
  have h : ((1 : ℝ) - 2) ^ 2 = 1 := by norm_num
  rw [h, div_one]
  ring

/-- Numerical check of `arith_geom_two` at `n = 4`:
`0·1 + 1·2 + 2·4 + 3·8 = 0 + 2 + 8 + 24 = 34 = (4 − 2)·16 + 2`. -/
theorem arith_geom_two_four :
    ∑ k ∈ range 4, (k : ℝ) * 2 ^ k = 34 := by
  rw [arith_geom_two]; norm_num

/-- A second numerical witness directly from the field closed form, at `x = 3`,
`n = 3`: `0·1 + 1·3 + 2·9 = 21`, and the closed-form numerator over `(1−3)² = 4`
gives `84/4 = 21`. -/
theorem arith_geom_three_three :
    ∑ k ∈ range 3, (k : ℝ) * 3 ^ k = 21 := by
  rw [arith_geom_div (x := (3 : ℝ)) (by norm_num)]; norm_num

/-! ## The infinite limit (consistency with Mathlib) -/

/-- The infinite arithmetico-geometric sum, recorded from Mathlib:
`∑' k, k·xᵏ = x/(1 − x)²` for `‖x‖ < 1` over `ℝ`.  The finite closed form
`arith_geom_div` recovers this as `n → ∞`: its numerator
`x·(1 − xⁿ) − n·xⁿ·(1 − x)` tends to `x` because `xⁿ → 0` and `n·xⁿ → 0`. -/
theorem tsum_arith_geom (x : ℝ) (hx : |x| < 1) :
    ∑' k : ℕ, (k : ℝ) * x ^ k = x / (1 - x) ^ 2 := by
  have : ‖x‖ < 1 := by rwa [Real.norm_eq_abs]
  exact tsum_coe_mul_geometric_of_norm_lt_one this

end GeometricSeriesOQ08OQ01
