import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-
# Third Moment of the Geometric Series: ∑ n³ rⁿ = r(1+4r+r²)/(1-r)⁴

## What This Proves

For a real ratio `r` with `‖r‖ < 1`,

  ∑_{n=0}^{∞} n³ · rⁿ  =  r(1 + 4r + r²) / (1-r)⁴.

This is the **third moment** of the geometric series, extending the low-order
moment family:

  ∑ rⁿ        = 1/(1-r)              (zeroth moment, the geometric series itself)
  ∑ n · rⁿ    = r/(1-r)²             (first moment)
  ∑ n² · rⁿ   = r(1+r)/(1-r)³        (second moment, `GeometricSeriesOQ07`)
  ∑ n³ · rⁿ   = r(1+4r+r²)/(1-r)⁴    (third moment — the new result here)

## Why This Is Not Already in Mathlib

Mathlib provides the zeroth and first moments directly
(`tsum_geometric_of_norm_lt_one`, `tsum_coe_mul_geometric_of_norm_lt_one`),
but has no closed form for `∑ n³ rⁿ`.  What it *does* provide is the family of
**rising-binomial** sums

  ∑_n (n+k choose k) · rⁿ = 1/(1-r)^{k+1}     (`hasSum_choose_mul_geometric_of_norm_lt_one`).

The contribution of this file is to assemble the third moment from the
`k = 0, 1, 2, 3` members of that family, using the polynomial identity in the
rising-binomial basis

  n³  =  6·(n+3 choose 3)  −  12·(n+2 choose 2)  +  7·(n+1 choose 1)  −  1.

This is the degree-3 analogue of the degree-2 identity `n² = 2·(n+2 choose 2) − 3n − 2`
used for the second moment.  The coefficients `(6, −12, 7, −1)` are obtained by
Newton's forward-difference expansion of `n³` against the basis
`{(n+k choose k)}` (the binomial transform of the sequence `n³`).

## Proof Strategy

1. Take four `HasSum` facts from Mathlib (the rising-binomial family at `k = 3, 2, 1, 0`):
   - `h₃ : ∑ (n+3 choose 3) rⁿ = 1/(1-r)⁴`
   - `h₂ : ∑ (n+2 choose 2) rⁿ = 1/(1-r)³`
   - `h₁ : ∑ (n+1 choose 1) rⁿ = 1/(1-r)²`
   - `h₀ : ∑ (n+0 choose 0) rⁿ = 1/(1-r)`
2. Form the linear combination `6·h₃ − 12·h₂ + 7·h₁ − 1·h₀`, whose summand is
   `n³ rⁿ` by the polynomial identity above.
3. Simplify the resulting value
   `6/(1-r)⁴ − 12/(1-r)³ + 7/(1-r)² − 1/(1-r)` to `r(1+4r+r²)/(1-r)⁴`
   with `field_simp; ring` (valid since `1 - r ≠ 0`), the algebraic core being
   `6 − 12(1-r) + 7(1-r)² − (1-r)³ = r(1+4r+r²)`.

## Probabilistic Interpretation

If `X` is geometric with `P(X = n) = (1-r) rⁿ` (`n ≥ 0`, `0 ≤ r < 1`), the first
three moments give `E[X] = r/(1-r)`, `E[X²] = r(1+r)/(1-r)²`, and
`E[X³] = r(1+4r+r²)/(1-r)³`, from which the skewness of the geometric
distribution can be read off.

## Status: 0 sorries, 0 axioms
-/

open Filter Topology

namespace GeometricSeriesOQ10

variable {r : ℝ}

/-! ## Casting the rising-binomial coefficients to ℝ -/

/-- `(n+3 choose 3) = (n+1)(n+2)(n+3)/6`, cast to `ℝ`.

Mathlib has `Nat.cast_choose_two` for the column-2 coefficient but no ready-made
cast for column 3, so we derive it from `Nat.cast_choose` (the factorial form)
together with the expansion `(n+3)! = (n+1)(n+2)(n+3) · n!`. -/
lemma cast_choose_three (n : ℕ) :
    ((n + 3).choose 3 : ℝ) = (n + 1) * (n + 2) * (n + 3) / 6 := by
  have hf : ((Nat.factorial (n + 3) : ℕ) : ℝ)
      = (n + 1) * (n + 2) * (n + 3) * (Nat.factorial n : ℕ) := by
    rw [Nat.factorial_succ (n + 2), Nat.factorial_succ (n + 1), Nat.factorial_succ n]
    push_cast
    ring
  have hn : ((Nat.factorial n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  rw [Nat.cast_choose ℝ (by omega : 3 ≤ n + 3), show n + 3 - 3 = n by omega, hf]
  have h3 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h3]
  field_simp

/-- The algebraic key in the rising-binomial basis:
`n³ = 6·(n+3 choose 3) − 12·(n+2 choose 2) + 7·(n+1 choose 1) − 1`, cast to `ℝ`. -/
lemma cube_eq (n : ℕ) :
    (n : ℝ) ^ 3 = 6 * ((n + 3).choose 3 : ℝ) - 12 * ((n + 2).choose 2 : ℝ)
      + 7 * ((n + 1).choose 1 : ℝ) - 1 := by
  rw [cast_choose_three, Nat.cast_choose_two, Nat.choose_one_right]
  push_cast
  ring

/-! ## The moment family -/

/-- **Zeroth moment** (the geometric series itself): `∑ rⁿ = 1/(1-r)`. -/
theorem tsum_geometric (hr : ‖r‖ < 1) :
    ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_one hr

/-- **First moment**: `∑ n · rⁿ = r/(1-r)²` (restatement of Mathlib's result,
included to display the full moment family). -/
theorem tsum_mul_geometric (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℝ) * r ^ n = r / (1 - r) ^ 2 :=
  tsum_coe_mul_geometric_of_norm_lt_one hr

/-! ## Third moment (the new result) -/

/-- `1 - r ≠ 0` whenever `‖r‖ < 1` (so `r ≠ 1`). -/
lemma one_sub_ne_zero (hr : ‖r‖ < 1) : (1 : ℝ) - r ≠ 0 :=
  sub_ne_zero.mpr fun h => by simp [← h] at hr

/-- **Third moment, `HasSum` form**: `∑ n³ · rⁿ = r(1+4r+r²)/(1-r)⁴`. -/
theorem hasSum_cube_mul_geometric (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n)
      (r * (1 + 4 * r + r ^ 2) / (1 - r) ^ 4) := by
  have hr1 : (1 : ℝ) - r ≠ 0 := one_sub_ne_zero hr
  -- Four members of the rising-binomial family.
  have h₃ : HasSum (fun n : ℕ => ((n + 3).choose 3 : ℝ) * r ^ n) (1 / (1 - r) ^ (3 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 3 hr
  have h₂ : HasSum (fun n : ℕ => ((n + 2).choose 2 : ℝ) * r ^ n) (1 / (1 - r) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have h₁ : HasSum (fun n : ℕ => ((n + 1).choose 1 : ℝ) * r ^ n) (1 / (1 - r) ^ (1 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 1 hr
  have h₀ : HasSum (fun n : ℕ => ((n + 0).choose 0 : ℝ) * r ^ n) (1 / (1 - r) ^ (0 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 0 hr
  -- Linear combination 6·h₃ − 12·h₂ + 7·h₁ − 1·h₀.
  have hcomb := (((h₃.mul_left 6).sub (h₂.mul_left 12)).add (h₁.mul_left 7)).sub (h₀.mul_left 1)
  -- Rewrite the summand as n³ rⁿ via the polynomial identity.
  have hfun : (fun n : ℕ => (n : ℝ) ^ 3 * r ^ n)
      = fun n : ℕ =>
          6 * (((n + 3).choose 3 : ℝ) * r ^ n) - 12 * (((n + 2).choose 2 : ℝ) * r ^ n)
            + 7 * (((n + 1).choose 1 : ℝ) * r ^ n) - 1 * (((n + 0).choose 0 : ℝ) * r ^ n) := by
    funext n
    have hc0 : ((n + 0).choose 0 : ℝ) = 1 := by simp
    rw [hc0, cube_eq n]
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
(`r(1+4r+r²)/(1-r)⁴ = (1/2)(1 + 2 + 1/4)/(1/2)⁴ = (1/2)(13/4)/(1/16) = (13/8)·16 = 26`.) -/
example : ∑' n : ℕ, (n : ℝ) ^ 3 * (1 / 2 : ℝ) ^ n = 26 := by
  rw [tsum_cube_mul_geometric (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

end GeometricSeriesOQ10
