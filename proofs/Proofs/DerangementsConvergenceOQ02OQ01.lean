/-
# Derangements: the nearest-integer characterization of the subfactorial

Open Question: derangements-convergence-oq-02-oq-01

The grandparent file `DerangementsConvergence.lean` proves the *magnitude* of the
approximation error
  |D(n)/n! - e⁻¹| ≤ 1/(n+1)!,
and the parent `DerangementsConvergenceOQ02.lean` pins down its *sign*.

This file draws the classical arithmetic consequence: the derangement number is
literally the **nearest integer** to `n!/e`.  Scaling the ratio bound by `n!`,
  |D(n) - n!·e⁻¹| ≤ n!/(n+1)! = 1/(n+1) ≤ 1/2   for n ≥ 1,
and the inequality is *strict* (`< 1/2`) once the single boundary value `n = 1`
is handled by the elementary bound `e⁻¹ < 1/2`.  A real number lying within
`1/2` of an integer rounds to that integer, so

  D(n) = round(n!/e)      for every n ≥ 1.

## Main Results

- `round_eq_of_abs_sub_lt_half` : reusable rounding criterion `|x - m| < ½ → round x = m`
- `exp_neg_one_lt_half` : the boundary estimate `e⁻¹ < 1/2`
- `abs_numDerangements_sub_lt_half` : `|D(n) - n!·e⁻¹| < 1/2` for `n ≥ 1` (strict)
- `numDerangements_eq_round` : **D(n) = round(n!/e)** for `n ≥ 1`
- `numDerangements_eq_floor` : the equivalent floor form `D(n) = ⌊n!·e⁻¹ + 1/2⌋`
- `round_factorial_exp_zero` / `numDerangements_round_ne_at_zero` : the identity
  genuinely fails at `n = 0` (`round(0!·e⁻¹) = 0 ≠ 1 = D(0)`), so the hypothesis
  `n ≥ 1` is **sharp**.

All results are fully machine-checked: no `sorry`, no `axiom` declarations, and
no structure-encoded assumptions (only Lean/Mathlib's foundational
`propext` / `Classical.choice` / `Quot.sound`).

## References

- Montmort (1708), Euler (1751) — derangement numbers
- The rounding identity `!n = round(n!/e)` is standard folklore for `n ≥ 1`.
-/

import Proofs.DerangementsConvergence
import Mathlib.Tactic

open Nat Real Filter Topology

noncomputable section

namespace DerangementsConvergenceOQ02OQ01

/- ## §1. A reusable rounding criterion -/

/-- If a real number `x` is within `1/2` of an integer `m`, then `round x = m`.
This is the elementary bridge from an analytic distance bound to an exact
integer identity. -/
lemma round_eq_of_abs_sub_lt_half {x : ℝ} {m : ℤ} (h : |x - (m : ℝ)| < 1 / 2) :
    round x = m := by
  rw [round_eq, Int.floor_eq_iff]
  rw [abs_sub_lt_iff] at h
  refine ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

/- ## §2. `e⁻¹ < 1/2` (the single boundary estimate) -/

/-- The reciprocal of `e` is strictly below `1/2`, because `e > 2`. -/
lemma exp_neg_one_lt_half : rexp (-1) < 1 / 2 := by
  have h2 : (2 : ℝ) < rexp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num)
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) h2

/- ## §3. The strict distance bound `|D(n) - n!·e⁻¹| < 1/2` -/

/-- The subfactorial `D(n)` lies strictly within `1/2` of `n!/e`, for every
`n ≥ 1`.  This is the heart of the nearest-integer characterization. -/
theorem abs_numDerangements_sub_lt_half (n : ℕ) (hn : 1 ≤ n) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| < 1 / 2 := by
  have hpos := factorial_cast_pos' n
  have hne := factorial_cast_ne_zero' n
  -- `D(n) - n!·e⁻¹ = n! · (D(n)/n! - e⁻¹)`.
  have hstep : (n.factorial : ℝ)
        * ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1))
      = (numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1) := by
    rw [mul_sub, ← mul_div_assoc, mul_div_cancel_left₀ (numDerangements n : ℝ) hne]
  rw [← hstep, abs_mul, abs_of_pos hpos]
  rcases eq_or_lt_of_le hn with h1 | h2
  · -- Boundary case `n = 1`: `D(1) = 0`, so the distance is exactly `e⁻¹ < 1/2`.
    rw [← h1]
    have hd : numDerangements 1 = 0 := rfl
    rw [hd]
    simp only [Nat.cast_zero, Nat.factorial_one, Nat.cast_one, zero_div, zero_sub,
      abs_neg, abs_of_pos (Real.exp_pos (-1)), one_mul]
    exact exp_neg_one_lt_half
  · -- Interior case `n ≥ 2`: the ratio bound gives `1/(n+1) ≤ 1/3 < 1/2`.
    have hrate := derangements_convergence_rate n
    have hbound : (n.factorial : ℝ)
        * |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)|
        ≤ (n.factorial : ℝ) * (1 / ((n + 1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hrate hpos.le
    have hval : (n.factorial : ℝ) * (1 / ((n + 1).factorial : ℝ))
        = 1 / ((n : ℝ) + 1) := by
      rw [Nat.factorial_succ]
      push_cast
      rw [mul_one_div, mul_comm ((n : ℝ) + 1) (n.factorial : ℝ), ← div_div,
        div_self hne]
    rw [hval] at hbound
    have hle3 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 / 3 := by
      apply one_div_le_one_div_of_le (by norm_num)
      have h2' : 2 ≤ n := h2
      have hcast : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h2'
      linarith
    linarith

/- ## §4. Main theorem: `D(n) = round(n!/e)` -/

/-- **Nearest-integer characterization of the subfactorial.**
For every `n ≥ 1`, the number of derangements of `n` objects is exactly the
nearest integer to `n!/e`. -/
theorem numDerangements_eq_round (n : ℕ) (hn : 1 ≤ n) :
    round ((n.factorial : ℝ) * rexp (-1)) = (numDerangements n : ℤ) := by
  apply round_eq_of_abs_sub_lt_half
  rw [abs_sub_comm,
    show ((numDerangements n : ℤ) : ℝ) = (numDerangements n : ℝ) by push_cast; ring]
  exact abs_numDerangements_sub_lt_half n hn

/-- The equivalent floor form: `D(n) = ⌊n!·e⁻¹ + 1/2⌋` for `n ≥ 1`. -/
theorem numDerangements_eq_floor (n : ℕ) (hn : 1 ≤ n) :
    ⌊(n.factorial : ℝ) * rexp (-1) + 1 / 2⌋ = (numDerangements n : ℤ) := by
  have h := numDerangements_eq_round n hn
  rwa [round_eq] at h

/- ## §5. Sharpness of the hypothesis `n ≥ 1` -/

/-- At `n = 0` the rounded value is `0`: the nearest integer to `0!/e = e⁻¹`
(≈ 0.3679) is `0`. -/
theorem round_factorial_exp_zero :
    round (((0 : ℕ).factorial : ℝ) * rexp (-1)) = 0 := by
  apply round_eq_of_abs_sub_lt_half
  simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Int.cast_zero, sub_zero,
    abs_of_pos (Real.exp_pos (-1))]
  exact exp_neg_one_lt_half

/-- **Sharpness.** The identity `D(n) = round(n!/e)` genuinely fails at `n = 0`:
there `round(0!·e⁻¹) = 0` while `D(0) = 1`.  Hence the hypothesis `n ≥ 1` in
`numDerangements_eq_round` cannot be dropped. -/
theorem numDerangements_round_ne_at_zero :
    round (((0 : ℕ).factorial : ℝ) * rexp (-1)) ≠ (numDerangements 0 : ℤ) := by
  rw [round_factorial_exp_zero]
  have hd : numDerangements 0 = 1 := rfl
  rw [hd]
  norm_num

end DerangementsConvergenceOQ02OQ01
