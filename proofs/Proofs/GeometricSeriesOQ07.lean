import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-
# Second Moment of the Geometric Series: ∑ n² rⁿ = r(1+r)/(1-r)³

## What This Proves

For a real ratio `r` with `‖r‖ < 1`,

  ∑_{n=0}^{∞} n² · rⁿ  =  r(1+r) / (1-r)³.

This is the **second moment** of the geometric series, completing the family of
low-order moments:

  ∑ rⁿ        = 1/(1-r)          (zeroth moment, the geometric series itself)
  ∑ n · rⁿ    = r/(1-r)²         (first moment)
  ∑ n² · rⁿ   = r(1+r)/(1-r)³    (second moment — the new result here)

## Why This Is Not Already in Mathlib

Mathlib provides the zeroth and first moments directly
(`tsum_geometric_of_norm_lt_one`, `tsum_coe_mul_geometric_of_norm_lt_one`),
but has no closed form for `∑ n² rⁿ`.  What it *does* provide is the family of
**rising-binomial** sums

  ∑_n (n+k choose k) · rⁿ = 1/(1-r)^{k+1}     (`hasSum_choose_mul_geometric_of_norm_lt_one`).

The contribution of this file is to assemble the second moment from the `k = 2`
member of that family together with the first moment and the bare geometric
series, using the polynomial identity

  n²  =  2·(n+2 choose 2)  −  3n  −  2,

which holds because `(n+2 choose 2) = (n+1)(n+2)/2`, so
`2·(n+2 choose 2) = n² + 3n + 2`.

## Proof Strategy

1. Take three `HasSum` facts from Mathlib:
   - `h₂ : ∑ (n+2 choose 2) rⁿ = 1/(1-r)³`
   - `h₁ : ∑ n rⁿ            = r/(1-r)²`
   - `h₀ : ∑ rⁿ              = (1-r)⁻¹`
2. Form the linear combination `2·h₂ − 3·h₁ − 2·h₀`, whose summand is
   `2(n+2 choose 2)rⁿ − 3n rⁿ − 2 rⁿ = n² rⁿ` by the identity above.
3. Simplify the resulting value `2/(1-r)³ − 3r/(1-r)² − 2/(1-r)` to `r(1+r)/(1-r)³`
   with `field_simp; ring` (valid since `1 - r ≠ 0`).

## Probabilistic Interpretation

If `X` is geometric with `P(X = n) = (1-r) rⁿ` (`n ≥ 0`, `0 ≤ r < 1`), then these
moments give `E[X] = r/(1-r)` and `E[X²] = r(1+r)/(1-r)²`, hence
`Var(X) = E[X²] − E[X]² = r/(1-r)²`.

## Status: 0 sorries, 0 axioms
-/

open Filter Topology

namespace GeometricSeriesOQ07

variable {r : ℝ}

/-! ## The polynomial identity behind the second moment -/

/-- The algebraic key: `n² = 2·(n+2 choose 2) − 3n − 2`, cast to `ℝ`.

Since `(n+2 choose 2) = (n+1)(n+2)/2`, we have `2·(n+2 choose 2) = n² + 3n + 2`,
so subtracting `3n + 2` recovers `n²`. -/
lemma two_choose_two_sub (n : ℕ) :
    (2 : ℝ) * ((n + 2).choose 2) - 3 * n - 2 = (n : ℝ) ^ 2 := by
  rw [Nat.cast_choose_two]
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

/-! ## Second moment (the new result) -/

/-- `1 - r ≠ 0` whenever `‖r‖ < 1` (so `r ≠ 1`). -/
lemma one_sub_ne_zero (hr : ‖r‖ < 1) : (1 : ℝ) - r ≠ 0 :=
  sub_ne_zero.mpr fun h => by simp [← h] at hr

/-- **Second moment, `HasSum` form**: `∑ n² · rⁿ = r(1+r)/(1-r)³`. -/
theorem hasSum_sq_mul_geometric (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) (r * (1 + r) / (1 - r) ^ 3) := by
  have hr1 : (1 : ℝ) - r ≠ 0 := one_sub_ne_zero hr
  -- Three Mathlib summation facts.
  have h₂ : HasSum (fun n : ℕ => ((n + 2).choose 2 : ℝ) * r ^ n) (1 / (1 - r) ^ (2 + 1)) :=
    hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have h₁ : HasSum (fun n : ℕ => (n : ℝ) * r ^ n) (r / (1 - r) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h₀ : HasSum (fun n : ℕ => r ^ n) ((1 - r)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hr
  -- Linear combination 2·h₂ − 3·h₁ − 2·h₀.
  have hcomb := ((h₂.mul_left 2).sub (h₁.mul_left 3)).sub (h₀.mul_left 2)
  -- Rewrite the summand as n² rⁿ via the polynomial identity.
  have hfun : (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n)
      = fun n : ℕ =>
          2 * (((n + 2).choose 2 : ℝ) * r ^ n) - 3 * ((n : ℝ) * r ^ n) - 2 * r ^ n := by
    funext n
    rw [← two_choose_two_sub n]
    ring
  rw [hfun]
  -- Functions now match; only the value needs simplification.
  convert hcomb using 1
  field_simp
  ring

/-- **Second moment, `tsum` form**: `∑ n² · rⁿ = r(1+r)/(1-r)³`. -/
theorem tsum_sq_mul_geometric (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℝ) ^ 2 * r ^ n = r * (1 + r) / (1 - r) ^ 3 :=
  (hasSum_sq_mul_geometric hr).tsum_eq

/-- The second-moment series is summable. -/
theorem summable_sq_mul_geometric (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) :=
  (hasSum_sq_mul_geometric hr).summable

/-! ## A concrete value -/

/-- Sanity check at `r = 1/2`: `∑ n²/2ⁿ = 6`.
(`r(1+r)/(1-r)³ = (1/2)(3/2)/(1/2)³ = (3/4)/(1/8) = 6`.) -/
example : ∑' n : ℕ, (n : ℝ) ^ 2 * (1 / 2 : ℝ) ^ n = 6 := by
  rw [tsum_sq_mul_geometric (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
  norm_num

end GeometricSeriesOQ07
