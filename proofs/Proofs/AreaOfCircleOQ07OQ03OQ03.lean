/-
# The half-integer Gamma ladder as even Gaussian moments

Research: area-of-circle-oq-07-oq-03-oq-03
Parent:   area-of-circle-oq-07-oq-03 (`Γ(1/2) = √π`, the Gamma shadow of the Gaussian integral)

The parent entry identified the single value `Γ(1/2) = √π` with the Gaussian
integral `∫_ℝ e^{-x²} dx = √π`.  This entry extends that one value to the whole
half-integer **ladder** and its probabilistic meaning: for every `n`, the even
Gaussian moment equals a half-integer Gamma value,

  `∫_ℝ x^{2n} e^{-x²} dx = Γ(n + 1/2)`,

and Mathlib's closed form `Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ` (`Real.Gamma_nat_add_half`)
then gives the moments in terms of double factorials.

Route: on the half-line the substitution `u = x²` turns `∫_{x>0} x^{2n} e^{-x²} dx`
into `½ Γ(n + 1/2)` — this is Mathlib's `integral_rpow_mul_exp_neg_rpow` with
`p = 2`, `q = 2n` — and even symmetry (`x^{2n} e^{-x²}` is even) doubles the
half-line integral to the whole line, cancelling the `½`.

Contributions:

* `gaussian_moment_eq_gamma` — the ladder `∫_ℝ x^{2n} e^{-x²} dx = Γ(n + 1/2)`.
* `gaussian_moment_closed` — the double-factorial closed form
  `∫_ℝ x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2ⁿ`.
* `gaussian_moment_zero` — `n = 0` recovers the parent's `∫_ℝ e^{-x²} dx = √π`.
* `gaussian_moment_two` — `n = 1` gives `∫_ℝ x² e^{-x²} dx = √π / 2`.

Everything here is `sorry`-free and `axiom`-free (only the foundational
`propext`/`Classical.choice`/`Quot.sound`; no `Lean.ofReduceBool`).
-/
import Mathlib

open Real Set MeasureTheory
open scoped Nat

namespace AreaOfCircleOQ07OQ03OQ03

/-- **The half-integer Gamma ladder as even Gaussian moments.**
`∫_ℝ x^{2n} e^{-x²} dx = Γ(n + 1/2)` for every `n`.

The half-line integral is `½ Γ(n + 1/2)` (the substitution `u = x²`, packaged as
`integral_rpow_mul_exp_neg_rpow` with `p = 2`, `q = 2n`), and even symmetry of the
integrand doubles it to the whole line. -/
theorem gaussian_moment_eq_gamma (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) = Real.Gamma (n + 1 / 2) := by
  -- integrability of the moment over all of ℝ (via the `rpow` form, using `rpow_natCast`)
  have hint : Integrable (fun x : ℝ => x ^ (2 * n) * Real.exp (-x ^ 2)) := by
    have hq : (-1 : ℝ) < ((2 * n : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
      (s := ((2 * n : ℕ) : ℝ)) hq
    refine h.congr ?_
    filter_upwards with x
    rw [Real.rpow_natCast, neg_one_mul]
  -- the half-line value, from the `u = x²` substitution lemma
  have hIoi : ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2)
      = 1 / 2 * Real.Gamma (n + 1 / 2) := by
    have hq : (-1 : ℝ) < ((2 * n : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ ((2 * n : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have key := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * n : ℕ) : ℝ))
      (by norm_num) hq
    have harg : (((2 * n : ℕ) : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 := by push_cast; ring
    rw [harg] at key
    rw [← key]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [Real.rpow_natCast, Real.rpow_two]
  -- even symmetry: the `Iic 0` half equals the `Ioi 0` half
  have hIic : ∫ x in Iic (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2)
      = ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun x : ℝ => x ^ (2 * n) * Real.exp (-x ^ 2))
    rw [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    show (-x) ^ (2 * n) * Real.exp (-(-x) ^ 2) = x ^ (2 * n) * Real.exp (-x ^ 2)
    have e1 : (-x) ^ (2 * n) = x ^ (2 * n) := by rw [pow_mul, neg_sq, ← pow_mul]
    rw [e1, neg_sq]
  -- split ℝ = Iic 0 ∪ Ioi 0 and combine
  have hsplit : ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2)
      = (∫ x in Iic (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2))
        + ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2) := by
    rw [← compl_Iic (a := (0 : ℝ))]
    exact (integral_add_compl measurableSet_Iic hint).symm
  rw [hsplit, hIic, ← two_mul, hIoi]
  ring

/-- **Double-factorial closed form.** `∫_ℝ x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2ⁿ`,
combining the ladder identity with Mathlib's `Real.Gamma_nat_add_half`. -/
theorem gaussian_moment_closed (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) = (2 * n - 1)‼ * √π / 2 ^ n := by
  rw [gaussian_moment_eq_gamma, Real.Gamma_nat_add_half]

/-- `n = 0` recovers the parent Gaussian integral `∫_ℝ e^{-x²} dx = √π`. -/
theorem gaussian_moment_zero : ∫ x : ℝ, Real.exp (-x ^ 2) = √π := by
  have h := gaussian_moment_eq_gamma 0
  rw [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq] at h
  simpa using h

/-- `n = 1`: the second even Gaussian moment `∫_ℝ x² e^{-x²} dx = √π / 2`. -/
theorem gaussian_moment_two : ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = √π / 2 := by
  have h := gaussian_moment_eq_gamma 1
  simp only [mul_one] at h
  rw [h, show ((1 : ℕ) : ℝ) + 1 / 2 = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

end AreaOfCircleOQ07OQ03OQ03
