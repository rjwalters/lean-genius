/-
  Derangements: D(n) = round(n!/e) for ALL n ≥ 1
  Open question: derangements-convergence-oq-06

  ## Context

  The parent file `DerangementsConvergence.lean` proves the convergence rate
    |D(n)/n! - e⁻¹| ≤ 1/(n+1)!,
  via the alternating-series estimation theorem. Multiplying by n! turns this
  into the integer-scale bound
    |D(n) - n!·e⁻¹| ≤ 1/(n+1).
  The sibling open question derangements-convergence-oq-03 used this to obtain
  the rounding identity D(n) = round(n!·e⁻¹) for n ≥ 2, where 1/(n+1) ≤ 1/3 < 1/2.

  ## What this file adds

  The soft bound 1/(n+1) is *strictly* below 1/2 only for n ≥ 2. At the boundary
  n = 1 it equals 1/2 exactly, so the generic "nearest integer" argument breaks
  down — the bound alone does not pin the rounding direction. This file closes
  that single remaining case using `e > 2` directly:
    1!/e = 1/e < 1/2   ⟹   round(1/e) = 0 = D(1),
  and combines it with the n ≥ 2 case to obtain the sharp statement: for EVERY
  n ≥ 1,
    D(n) = round(n!/e).

  The development is **self-contained**: it depends only on the parent's rate
  bound `derangements_convergence_rate` (not on the n ≥ 2 sibling file), and it
  re-derives the n ≥ 2 case as well, so it is a complete standalone proof of the
  full n ≥ 1 statement.

  We record both the `n!·e⁻¹` form and the literal division form `n!/e`, and we
  note that the identity FAILS at n = 0 (D(0) = 1 but round(0!/e) = round(1/e)
  = 0), so `n ≥ 1` is the sharp range.

  ## Main results
  - `round_eq_of_abs_lt_half`      : |x - m| < 1/2 ⟹ round x = m (m : ℤ)
  - `abs_sub_le`                   : |D(n) - n!·e⁻¹| ≤ 1/(n+1)        (all n)
  - `rexp_neg_one_lt_half`         : 1/e < 1/2  (from e > 2)
  - `abs_sub_lt_half`              : |D(n) - n!·e⁻¹| < 1/2, for n ≥ 1 (incl. boundary)
  - `numDerangements_eq_round`     : D(n) = round(n!·e⁻¹), for n ≥ 1 (unified)
  - `numDerangements_eq_round_div` : D(n) = round(n!/e),   for n ≥ 1 (division form)
  - `round_factorial_div_e_at_zero`: sharpness — the identity fails at n = 0
-/
import Mathlib
import Proofs.DerangementsConvergence

open Nat Real Filter Topology

namespace DerangementsConvergenceOQ06

/-- If a real `x` is within `1/2` of an integer `m`, then `round x = m`. This is
    the "nearest integer" characterisation we use throughout. We qualify
    `Int.floor_eq_iff` explicitly (under `open Nat`, the bare name resolves to
    `Nat.floor_eq_iff`, which has a different statement). -/
lemma round_eq_of_abs_lt_half {x : ℝ} {m : ℤ} (h : |x - (m : ℝ)| < 1 / 2) :
    round x = m := by
  rw [round_eq]
  rw [abs_sub_lt_iff] at h
  apply Int.floor_eq_iff.mpr
  refine ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

/-- **Integer-scale rate bound.** Multiplying the parent's
    `|D(n)/n! - e⁻¹| ≤ 1/(n+1)!` by `n!` gives `|D(n) - n!·e⁻¹| ≤ 1/(n+1)`. -/
lemma abs_sub_le (n : ℕ) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| ≤ 1 / (n + 1 : ℝ) := by
  have hrate := derangements_convergence_rate n
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr n.factorial_pos
  have hne : (n.factorial : ℝ) ≠ 0 := hfac.ne'
  have e : (numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)
      = ((numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)) * (n.factorial : ℝ) := by
    field_simp
  rw [e, abs_mul, abs_of_pos hfac]
  have hstep :
      |(numDerangements n : ℝ) / (n.factorial : ℝ) - rexp (-1)| * (n.factorial : ℝ)
        ≤ (1 / ((n + 1).factorial : ℝ)) * (n.factorial : ℝ) :=
    mul_le_mul_of_nonneg_right hrate hfac.le
  refine hstep.trans (le_of_eq ?_)
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- `1/e = e⁻¹ < 1/2`, because `e > 2`. This is the ingredient that makes the
    boundary case `n = 1` work, where the soft bound `1/(n+1) = 1/2` is not
    strict. -/
lemma rexp_neg_one_lt_half : rexp (-1) < 1 / 2 := by
  have h2 : (2 : ℝ) < rexp 1 := by have := Real.exp_one_gt_d9; linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_lt_one_div_of_lt (by norm_num) h2

/-- The nearest integer to `e⁻¹ = 1/e ≈ 0.3679` is `0`. -/
lemma round_rexp_neg_one : round (rexp (-1)) = 0 := by
  apply round_eq_of_abs_lt_half
  rw [Int.cast_zero, sub_zero, abs_of_pos (Real.exp_pos _)]
  exact rexp_neg_one_lt_half

/-- **The strict bound, including the boundary.** For every `n ≥ 1`,
    `|D(n) - n!·e⁻¹| < 1/2`. For `n ≥ 2` this follows from `1/(n+1) ≤ 1/3`; for
    `n = 1` it uses `1/e < 1/2` directly. -/
lemma abs_sub_lt_half (n : ℕ) (hn : 1 ≤ n) :
    |(numDerangements n : ℝ) - (n.factorial : ℝ) * rexp (-1)| < 1 / 2 := by
  rcases eq_or_lt_of_le hn with h1 | h2
  · -- n = 1 (boundary)
    subst h1
    have hd : (numDerangements 1 : ℝ) = 0 := by
      norm_num [show numDerangements 1 = 0 from rfl]
    rw [hd, Nat.factorial_one, Nat.cast_one, one_mul, zero_sub, abs_neg,
        abs_of_pos (Real.exp_pos _)]
    exact rexp_neg_one_lt_half
  · -- n ≥ 2
    have hb := abs_sub_le n
    have hlt : (1 : ℝ) / (n + 1) < 1 / 2 := by
      apply one_div_lt_one_div_of_lt (by norm_num)
      have : (2 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast (show 2 < n + 1 by omega)
      exact this
    linarith [hb, hlt]

/-- **Derangements are the nearest integer to `n!/e`, for every `n ≥ 1`.**
    `(numDerangements n : ℤ) = round(n!·e⁻¹)`. -/
theorem numDerangements_eq_round (n : ℕ) (hn : 1 ≤ n) :
    (numDerangements n : ℤ) = round ((n.factorial : ℝ) * rexp (-1)) := by
  symm
  apply round_eq_of_abs_lt_half
  rw [abs_sub_comm]
  push_cast
  exact abs_sub_lt_half n hn

/-- **Literal division form.** `D(n) = round(n!/e)` for every `n ≥ 1`, with the
    argument written as the actual quotient `n!/e` rather than `n!·e⁻¹`. -/
theorem numDerangements_eq_round_div (n : ℕ) (hn : 1 ≤ n) :
    (numDerangements n : ℤ) = round ((n.factorial : ℝ) / Real.exp 1) := by
  have hform : (n.factorial : ℝ) / Real.exp 1 = (n.factorial : ℝ) * rexp (-1) := by
    rw [Real.exp_neg]; ring
  rw [hform]
  exact numDerangements_eq_round n hn

/-- **Sharpness at the lower end.** The identity `D(n) = round(n!/e)` FAILS at
    `n = 0`: here `D(0) = 1` (the empty permutation is vacuously a derangement)
    but `round(0!/e) = round(1/e) = 0`. Hence `n ≥ 1` is the sharp range. -/
theorem round_factorial_div_e_at_zero :
    (numDerangements 0 : ℤ) = 1 ∧
      round ((Nat.factorial 0 : ℝ) / Real.exp 1) = 0 := by
  refine ⟨by norm_num [show numDerangements 0 = 1 from rfl], ?_⟩
  have hform : (Nat.factorial 0 : ℝ) / Real.exp 1 = rexp (-1) := by
    rw [Real.exp_neg]; norm_num
  rw [hform, round_rexp_neg_one]

end DerangementsConvergenceOQ06
