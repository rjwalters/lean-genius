import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# Second-order Arithmetico-Geometric Sum: a closed form for ∑ k²·xᵏ

## What This Proves

For a ratio `x` and a length `n`, the *second-order* arithmetico-geometric
finite sum `∑_{k=0}^{n-1} k²·xᵏ` (each geometric term `xᵏ` weighted by the
square `k²`) has the division-free closed form

  (1 − x)³ · ∑_{k=0}^{n-1} k²·xᵏ
      =  x + x² − n²·xⁿ + (2n² − 2n − 1)·x^{n+1} − (n−1)²·x^{n+2},

valid over **any** commutative ring, and the corresponding field closed form

  ∑_{k=0}^{n-1} k²·xᵏ
      =  (x + x² − n²·xⁿ + (2n² − 2n − 1)·x^{n+1} − (n−1)²·x^{n+2}) / (1 − x)³
                                                                   (x ≠ 1).

This is the next member of the weight family `∑ kᵐ·xᵏ` after the unweighted
geometric sum (`m = 0`, ancestor `geometric-series-oq-08`) and the linear
arithmetico-geometric sum (`m = 1`, parent `geometric-series-oq-08-oq-01`,
`(1 − x)²·∑ k·xᵏ = x(1 − xⁿ) − n·xⁿ(1 − x)`).

The **infinite** second-order series `∑' k, k²·xᵏ = x(1+x)/(1−x)³` (`‖x‖ < 1`)
is the `n → ∞` limit of this finite closed form (the tail terms `n²·xⁿ`,
`n²·x^{n+1}`, `n²·x^{n+2}` all vanish), leaving `(x + x²)/(1 − x)³`.  That
infinite value is *already* in the gallery as `geometric-series-oq-07`
(`tsum_sq_mul_geometric`), so it is **not** reproved here; this entry supplies
the missing *finite* companion and cross-references oq-07 for the limit.

## Why This Is Not Already in Mathlib

Mathlib records the infinite linear weighted series
`tsum_coe_mul_geometric_of_norm_lt_one` (`∑' n, n·rⁿ = r/(1−r)²`) and the
`choose`-weighted family `tsum_choose_mul_geometric_of_norm_lt_one`
(`∑' n, C(n+k,k)·rⁿ = 1/(1−r)^{k+1}`), plus the plain finite geometric sum
`geom_sum_eq`.  It does **not** record the *finite* second-order
arithmetico-geometric closed form `∑_{k<n} k²·xᵏ`, which is supplied here.

## Proof Strategy

1. **Ring identity (`sq_arith_geom_mul`).** Induction on `n`.  The base case is
   `0 = 0`; the step uses `Finset.sum_range_succ` to peel the `k = n` term and
   then `push_cast; ring`.  Coefficients are written with ring casts
   (`(n : R)`, `(n : R) − 1`) so the `n = 0` instance is well-defined (no ℕ
   truncated subtraction).
2. **Field form (`sq_arith_geom_div`).** Clear `(1 − x)³ ≠ 0` (from `x ≠ 1`)
   with `eq_div_iff` and discharge by the ring identity.
3. **Specialisations / numeric witnesses.** `x = 2` and direct numeric checks
   at `n = 4` (`0 + 1·2 + 4·4 + 9·8 = 90`) and `x = 3, n = 3` (`= 39`).

All results depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace GeometricSeriesOQ08OQ01OQ01

open Finset

/-! ## The finite second-order arithmetico-geometric sum -/

/-- **Division-free closed form** for the finite second-order
arithmetico-geometric sum, valid over any commutative ring:
`(1 − x)³ · ∑_{k<n} k²·xᵏ = x + x² − n²·xⁿ + (2n² − 2n − 1)·x^{n+1} − (n−1)²·x^{n+2}`.
Proved by induction on `n`: peel the top term with `Finset.sum_range_succ`, then
`push_cast; ring`. -/
theorem sq_arith_geom_mul {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (1 - x) ^ 3 * ∑ k ∈ range n, (k : R) ^ 2 * x ^ k
      = x + x ^ 2 - (n : R) ^ 2 * x ^ n
        + (2 * (n : R) ^ 2 - 2 * (n : R) - 1) * x ^ (n + 1)
        - ((n : R) - 1) ^ 2 * x ^ (n + 2) := by
  induction n with
  | zero => simp only [range_zero, sum_empty, mul_zero, Nat.cast_zero]; ring
  | succ n ih =>
      rw [sum_range_succ, mul_add, ih]
      push_cast
      ring

/-- **Field closed form** for the finite second-order arithmetico-geometric sum
(`x ≠ 1`):
`∑_{k<n} k²·xᵏ = (x + x² − n²·xⁿ + (2n² − 2n − 1)·x^{n+1} − (n−1)²·x^{n+2}) / (1 − x)³`. -/
theorem sq_arith_geom_div {K : Type*} [Field K] (x : K) (hx : x ≠ 1) (n : ℕ) :
    ∑ k ∈ range n, (k : K) ^ 2 * x ^ k
      = (x + x ^ 2 - (n : K) ^ 2 * x ^ n
          + (2 * (n : K) ^ 2 - 2 * (n : K) - 1) * x ^ (n + 1)
          - ((n : K) - 1) ^ 2 * x ^ (n + 2)) / (1 - x) ^ 3 := by
  have h1 : (1 : K) - x ≠ 0 := sub_ne_zero.mpr hx.symm
  have h2 : (1 - x) ^ 3 ≠ 0 := pow_ne_zero _ h1
  rw [eq_div_iff h2, mul_comm]
  exact sq_arith_geom_mul x n

/-- Sanity check of the ring identity at `n = 1` (both sides `0`): the only term
is `0²·x⁰ = 0`.  Recorded as a guard against off-by-one sign errors. -/
theorem sq_arith_geom_mul_one {R : Type*} [CommRing R] (x : R) :
    (1 - x) ^ 3 * ∑ k ∈ range 1, (k : R) ^ 2 * x ^ k = 0 := by
  rw [sq_arith_geom_mul]; ring

/-! ## Specialisations and numeric witnesses -/

/-- The weight-`x = 2` specialisation, from the field closed form.  Here
`(1 − 2)³ = −1`, so `∑_{k<n} k²·2ᵏ = −(2 + 4 − n²·2ⁿ + (2n² − 2n − 1)·2^{n+1}
− (n − 1)²·2^{n+2})`. -/
theorem sq_arith_geom_two (n : ℕ) :
    ∑ k ∈ range n, (k : ℝ) ^ 2 * 2 ^ k
      = (n : ℝ) ^ 2 * 2 ^ n
        - (2 * (n : ℝ) ^ 2 - 2 * (n : ℝ) - 1) * 2 ^ (n + 1)
        + ((n : ℝ) - 1) ^ 2 * 2 ^ (n + 2) - 6 := by
  rw [sq_arith_geom_div (x := (2 : ℝ)) (by norm_num)]
  have h : ((1 : ℝ) - 2) ^ 3 = -1 := by norm_num
  rw [h]
  field_simp
  ring

/-- Numerical check at `n = 4`:
`0²·1 + 1²·2 + 2²·4 + 3²·8 = 0 + 2 + 16 + 72 = 90`. -/
theorem sq_arith_geom_two_four :
    ∑ k ∈ range 4, (k : ℝ) ^ 2 * 2 ^ k = 90 := by
  rw [sq_arith_geom_two]; norm_num

/-- A second numerical witness directly from the field closed form, at `x = 3`,
`n = 3`: `0²·1 + 1²·3 + 2²·9 = 0 + 3 + 36 = 39`. -/
theorem sq_arith_geom_three_three :
    ∑ k ∈ range 3, (k : ℝ) ^ 2 * 3 ^ k = 39 := by
  rw [sq_arith_geom_div (x := (3 : ℝ)) (by norm_num)]; norm_num

/-! ## The infinite limit (recorded elsewhere)

The `n → ∞` limit of the finite closed form is the infinite second-order
weighted series `∑' k, k²·xᵏ = x(1+x)/(1−x)³` for `‖x‖ < 1`: the tail terms
`n²·xⁿ`, `(2n²−2n−1)·x^{n+1}`, `(n−1)²·x^{n+2}` all tend to `0`, leaving the
numerator `x + x²`.  That infinite value is already in the gallery as
`geometric-series-oq-07` (`GeometricSeriesOQ07.tsum_sq_mul_geometric`) and is
**not** reproved here. -/

end GeometricSeriesOQ08OQ01OQ01
