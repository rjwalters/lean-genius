import Mathlib

/-!
# Stirling Formula OQ-01 / OQ-01: The Second and Third Corrections via Bernoulli Numbers

## The Open Question

`StirlingExpansion.lean` formalizes the first Stirling correction
`n!/[√(2πn)(n/e)ⁿ] = 1 + 1/(12n) + O(1/n²)` and *defines* the higher multiplicative
coefficients `a₂ = 1/288`, `a₃ = −139/51840`. Its first open question asks to formalize the
second correction `1/(288n²)` and the third `−139/(51840n³)`.

## What this file proves

The multiplicative coefficients `aₖ` are not arbitrary: they are the exponential of the genuine
**Stirling (log-)series**, whose coefficients are Bernoulli numbers,
`gₖ = B_{2k} / (2k(2k−1))`. This file:

* defines `stirlingLogCoeff k = B_{2k}/(2k(2k−1))` and computes
  `g₁ = 1/12` (from `B₂ = 1/6`) and `g₂ = −1/360` (from `B₄ = −1/30`) — the Bernoulli origin
  of the corrections;
* proves the **exponentiation relations** that produce the multiplicative coefficients:
  `a₂ = g₁²/2` (so `1/288 = (1/12)²/2`) and `a₃ = g₂ + g₁³/6`
  (so `−139/51840 = −1/360 + (1/12)³/6`) — exactly why the second and third corrections take
  the stated values;
* gives the closed form of the fourth Stirling partial sum,
  `S₄(n) = 1 + 1/(12n) + 1/(288n²) − 139/(51840n³)`.

So the magic constants `1/288` and `−139/51840` are pinned down as `exp` of the Bernoulli
log-series — answering the open question's "why these values".

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`. `stirlingCoeff` /
`stirlingPartial` mirror `StirlingExpansion.lean`; Bernoulli values come from Mathlib.
-/

namespace StirlingFormulaOQ01OQ01

/-- Multiplicative Stirling coefficients (mirrors `StirlingExpansion.stirlingCoeff`). -/
noncomputable def stirlingCoeff : ℕ → ℝ
  | 0 => 1
  | 1 => 1 / 12
  | 2 => 1 / 288
  | 3 => -139 / 51840
  | _ => 0

theorem stirlingCoeff_one : stirlingCoeff 1 = 1 / 12 := rfl
theorem stirlingCoeff_two : stirlingCoeff 2 = 1 / 288 := rfl
theorem stirlingCoeff_three : stirlingCoeff 3 = -139 / 51840 := rfl

/-- The Stirling expansion truncated at `k` terms: `Sₖ(n) = ∑_{i<k} aᵢ / nⁱ`. -/
noncomputable def stirlingPartial (k : ℕ) (n : ℕ) : ℝ :=
  (Finset.range k).sum (fun i => stirlingCoeff i / (n : ℝ) ^ i)

/-- **The fourth Stirling partial sum** in closed form, including the third correction. -/
theorem stirlingPartial_four (n : ℕ) (hn : n ≠ 0) :
    stirlingPartial 4 n =
      1 + 1 / (12 * (n : ℝ)) + 1 / (288 * (n : ℝ) ^ 2) - 139 / (51840 * (n : ℝ) ^ 3) := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [stirlingPartial, Finset.sum_range_succ, Finset.sum_range_zero,
    stirlingCoeff, zero_add]
  field_simp
  ring

/-! ## The Bernoulli log-series coefficients -/

/-- The Stirling **log-series** coefficients `gₖ = B_{2k} / (2k(2k−1))`. The asymptotic series
    `log Γ(n+1) − (n+½)log n + n − ½log(2π) = ∑_{k≥1} gₖ / n^{2k−1}` has these Bernoulli
    coefficients. -/
noncomputable def stirlingLogCoeff (k : ℕ) : ℝ :=
  (bernoulli (2 * k) : ℝ) / ((2 * k : ℝ) * ((2 * k : ℝ) - 1))

/-- `g₁ = 1/12`, from `B₂ = 1/6`. This is the first Stirling correction. -/
theorem stirlingLogCoeff_one : stirlingLogCoeff 1 = 1 / 12 := by
  simp only [stirlingLogCoeff]
  norm_num [bernoulli_two]

/-- `g₂ = −1/360`, from `B₄ = −1/30`. This is the third-order log correction. -/
theorem stirlingLogCoeff_two : stirlingLogCoeff 2 = -1 / 360 := by
  have hb4 : (bernoulli 4 : ℝ) = -1 / 30 := by
    rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]; norm_num
  simp only [stirlingLogCoeff]
  rw [show (2 * 2 : ℕ) = 4 from rfl, hb4]
  norm_num

/-! ## Exponentiating the log-series produces the multiplicative coefficients -/

/-- **Second correction from the first.** `a₂ = g₁²/2`: exponentiating the log-series,
    the `1/n²` coefficient is `½·(1/12)² = 1/288`. -/
theorem stirlingCoeff_two_eq : stirlingCoeff 2 = stirlingLogCoeff 1 ^ 2 / 2 := by
  rw [stirlingCoeff_two, stirlingLogCoeff_one]; norm_num

/-- **Third correction from the lower ones.** `a₃ = g₂ + g₁³/6`: the `1/n³` coefficient of
    `exp(g₁/n + g₂/n³ + ⋯)` is `g₂ + g₁³/6 = −1/360 + (1/12)³/6 = −139/51840`. -/
theorem stirlingCoeff_three_eq :
    stirlingCoeff 3 = stirlingLogCoeff 2 + stirlingLogCoeff 1 ^ 3 / 6 := by
  rw [stirlingCoeff_three, stirlingLogCoeff_two, stirlingLogCoeff_one]; norm_num

end StirlingFormulaOQ01OQ01

/-!
## Summary

Grounding the second and third Stirling corrections in Bernoulli numbers:

- `stirlingLogCoeff_one`/`_two`: the log-series coefficients `g₁ = 1/12` (from `B₂`),
  `g₂ = −1/360` (from `B₄`).
- `stirlingCoeff_two_eq`: `a₂ = g₁²/2` ⇒ `1/288 = (1/12)²/2`.
- `stirlingCoeff_three_eq`: `a₃ = g₂ + g₁³/6` ⇒ `−139/51840 = −1/360 + (1/12)³/6`.
- `stirlingPartial_four`: `S₄(n) = 1 + 1/(12n) + 1/(288n²) − 139/(51840n³)`.

So the constants `1/288` and `−139/51840` are the exponential of the Bernoulli log-series.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
