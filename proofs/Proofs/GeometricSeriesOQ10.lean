import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-
# Third Moment of the Geometric Series: ∑ n³ rⁿ = r(1+4r+r²)/(1-r)⁴

## What This Proves

For a real ratio `r` with `‖r‖ < 1`,

  ∑_{n=0}^{∞} n³ · rⁿ  =  r(1 + 4r + r²) / (1-r)⁴.

This is the **third moment** of the geometric series, extending the moment family
proved in `GeometricSeriesOQ07.lean` (second moment) one step further:

  ∑ rⁿ        = 1/(1-r)               (zeroth moment, the geometric series itself)
  ∑ n · rⁿ    = r/(1-r)²              (first moment)
  ∑ n² · rⁿ   = r(1+r)/(1-r)³         (second moment, OQ07)
  ∑ n³ · rⁿ   = r(1+4r+r²)/(1-r)⁴     (third moment — the new result here)

## Why This Is Not Already in Mathlib

Mathlib provides the zeroth and first moments directly
(`tsum_geometric_of_norm_lt_one`, `tsum_coe_mul_geometric_of_norm_lt_one`),
but has no closed form for `∑ n³ rⁿ`.  What it *does* provide is the family of
**rising-binomial** sums

  ∑_n (n+k choose k) · rⁿ = 1/(1-r)^{k+1}     (`hasSum_choose_mul_geometric_of_norm_lt_one`).

The contribution of this file is to assemble the third moment from the `k = 3`
member of that family, together with the `k = 2` member, the first moment, and the
bare geometric series, using the polynomial identity

  n³  =  6·(n+3 choose 3)  −  12·(n+2 choose 2)  +  7n  +  6.

This is the degree-3 analogue of the degree-2 identity `n² = 2·(n+2 choose 2) − 3n − 2`
used for the second moment.  It holds because `(n+3 choose 3) = (n+1)(n+2)(n+3)/6`
and `(n+2 choose 2) = (n+1)(n+2)/2`, so

  6·(n+3 choose 3) = n³ + 6n² + 11n + 6  and  12·(n+2 choose 2) = 6n² + 18n + 12,

whose difference is `n³ − 7n − 6`, recovered by adding `7n + 6`.

## Proof Strategy

1. Take four `HasSum` facts from Mathlib:
   - `h₃ : ∑ (n+3 choose 3) rⁿ = 1/(1-r)⁴`
   - `h₂ : ∑ (n+2 choose 2) rⁿ = 1/(1-r)³`
   - `h₁ : ∑ n rⁿ            = r/(1-r)²`
   - `h₀ : ∑ rⁿ              = (1-r)⁻¹`
2. Form the linear combination `6·h₃ − 12·h₂ + 7·h₁ + 6·h₀`, whose summand is
   `n³ rⁿ` by the identity above.
3. Simplify the resulting value
   `6/(1-r)⁴ − 12/(1-r)³ + 7r/(1-r)² + 6/(1-r)` to `r(1+4r+r²)/(1-r)⁴`
   with `field_simp; ring` (valid since `1 − r ≠ 0`).  The numerator collapses to
   `r + 4r² + r³ = r(1 + 4r + r²)`.

## Probabilistic Interpretation

If `X` is geometric with `P(X = n) = (1-r) rⁿ` (`n ≥ 0`, `0 ≤ r < 1`), the third
moment `E[X³] = r(1+4r+r²)/(1-r)³` is the next ingredient after `E[X]`, `E[X²]`
for computing the skewness of the geometric distribution.

## Status: 0 sorries, 0 axioms
-/

open Filter Topology

namespace GeometricSeriesOQ10

variable {r : ℝ}

/-! ## The cast of the rising binomial coefficient `(n+3 choose 3)`

Mathlib has `Nat.cast_choose_two` but no `cast_choose_three`, so we derive the
required real value from `Nat.descFactorial_eq_factorial_mul_choose`:
`(n+3).descFactorial 3 = 3! · (n+3 choose 3)`, and the descending factorial
`(n+3).descFactorial 3` evaluates to `(n+1)(n+2)(n+3)`. -/

/-- `6·(n+3 choose 3) = (n+1)(n+2)(n+3)`, cast to `ℝ`. -/
lemma cast_six_choose_three (n : ℕ) :
    6 * ((n + 3).choose 3 : ℝ) = (n + 1) * (n + 2) * (n + 3) := by
  have h : (n + 3).descFactorial 3 = 6 * (n + 3).choose 3 := by
    have := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3
    simpa [Nat.factorial] using this
  have e0 : n + 3 - 0 = n + 3 := by omega
  have e1 : n + 3 - 1 = n + 2 := by omega
  have e2 : n + 3 - 2 = n + 1 := by omega
  have h2 : (n + 3).descFactorial 3 = (n + 1) * (n + 2) * (n + 3) := by
    simp only [Nat.descFactorial, e0, e1, e2, mul_one]
    ring
  rw [h2] at h
  exact_mod_cast h.symm

/-! ## The polynomial identity behind the third moment -/

/-- The algebraic key: `6·(n+3 choose 3) − 12·(n+2 choose 2) + 7n + 6 = n³`, cast to `ℝ`. -/
lemma cube_combo (n : ℕ) :
    6 * ((n + 3).choose 3 : ℝ) - 12 * ((n + 2).choose 2 : ℝ) + 7 * n + 6 = (n : ℝ) ^ 3 := by
  rw [cast_six_choose_three n, Nat.cast_choose_two]
  push_cast
  ring

/-! ## The moment family -/

/-- **Zeroth moment** (the geometric series itself): `∑ rⁿ = 1/(1-r)`. -/
theorem tsum_geometric (hr : ‖r‖ < 1) :
    ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_one hr

/-- **First moment**: `∑ n · rⁿ = r/(1-r)²` (restatement of Mathlib's result). -/
theorem tsum_mul_geometric (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℝ) * r ^ n = r / (1 - r) ^ 2 :=
  tsum_coe_mul_geometric_of_norm_lt_one hr

/-! ## Third moment (the new result) -/

/-- `1 - r ≠ 0` whenever `‖r‖ < 1` (so `r ≠ 1`). -/
lemma one_sub_ne_zero (hr : ‖r‖ < 1) : (1 : ℝ) - r ≠ 0 :=
  sub_ne_zero.mpr fun h => by simp [← h] at hr

/-- **Third moment, `HasSum` form**: `∑ n³ · rⁿ = r(1+4r+r²)/(1-r)⁴`. -/
theorem hasSum_cube_mul_geometric (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n) (r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4) := by
  have hr1 : (1 : ℝ) - r ≠ 0 := one_sub_ne_zero hr
  -- Four Mathlib summation facts.
  have h₃ : HasSum (fun n : ℕ => ((n + 3).choose 3 : ℝ) * r ^ n) (1 / (1 - r) ^ (3 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 3 hr
  have h₂ : HasSum (fun n : ℕ => ((n + 2).choose 2 : ℝ) * r ^ n) (1 / (1 - r) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have h₁ : HasSum (fun n : ℕ => (n : ℝ) * r ^ n) (r / (1 - r) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h₀ : HasSum (fun n : ℕ => r ^ n) ((1 - r)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hr
  -- Linear combination 6·h₃ − 12·h₂ + 7·h₁ + 6·h₀.
  have hcomb := (((h₃.mul_left 6).sub (h₂.mul_left 12)).add (h₁.mul_left 7)).add (h₀.mul_left 6)
  -- Rewrite the summand as n³ rⁿ via the polynomial identity.
  have hfun : (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n)
      = fun n : ℕ =>
          6 * (((n + 3).choose 3 : ℝ) * r ^ n) - 12 * (((n + 2).choose 2 : ℝ) * r ^ n)
            + 7 * ((n : ℝ) * r ^ n) + 6 * r ^ n := by
    funext n
    rw [← cube_combo n]
    ring
  rw [hfun]
  -- Functions now match; only the value needs simplification.
  convert hcomb using 1
  field_simp
  ring

/-- **Third moment, `tsum` form**: `∑ n³ · rⁿ = r(1+4r+r²)/(1-r)⁴`. -/
theorem tsum_cube_mul_geometric (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℝ) ^ 3 * r ^ n = r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4 :=
  (hasSum_cube_mul_geometric hr).tsum_eq

/-- The third-moment series is summable. -/
theorem summable_cube_mul_geometric (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n) :=
  (hasSum_cube_mul_geometric hr).summable

/-! ## A concrete value -/

/-- Sanity check at `r = 1/2`: `∑ n³/2ⁿ = 26`.
(`r(1+4r+r²)/(1-r)⁴ = (1/2)(1+2+1/4)/(1/2)⁴ = (13/8)/(1/16) = 26`.) -/
example : ∑' n : ℕ, (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ n = 26 := by
  rw [tsum_cube_mul_geometric (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

end GeometricSeriesOQ10
