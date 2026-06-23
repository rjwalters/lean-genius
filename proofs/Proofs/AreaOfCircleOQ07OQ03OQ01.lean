import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-
# The half-integer Gamma ladder as even Gaussian moments

## Open Question (area-of-circle-oq-07-oq-03-oq-01)
The parent entry `area-of-circle-oq-07-oq-03` proves `Γ(1/2) = √π`, the
Gamma-function shadow of the Gaussian integral `∫_ℝ e^{-x²} = √π`.  This entry
climbs the *half-integer ladder*: it evaluates `Γ(n + 1/2)` for every natural
`n`, exhibiting the closed form

    Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ,

and — the genuinely new content — identifies these half-integer Gamma values
with the **even Gaussian moments**

    ∫_ℝ x^{2n} e^{-x²} dx = Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ.

## What Mathlib already has, and what is new

Mathlib's `Real.Gamma_nat_add_half` records the closed form
`Γ(k + 1/2) = (2k-1)‼ · √π / 2ᵏ`, so the bare ladder is a re-export.  What
Mathlib does *not* package is the **moment identity**: that this same number is
the integral of `x^{2n} e^{-x²}` over the line.  That is the substance proved
here.

## Proof of the moment identity

The half-line moment is the `u = x²` substitution applied to Euler's integral:
with `s = n + 1/2`,

    Γ(n + 1/2) = ∫₀^∞ u^{n-1/2} e^{-u} du           (`Real.Gamma_eq_integral`)
               = ∫₀^∞ (2x)·x^{2n-1} e^{-x²} dx       (`u = x²`, via
                                                       `integral_comp_rpow_Ioi_of_pos`)
               = 2 ∫₀^∞ x^{2n} e^{-x²} dx.

So the half-line moment is `Γ(n + 1/2)/2`.  Because `x ↦ x^{2n} e^{-x²}` is even,
the full-line integral doubles the half-line one (`integral_comp_abs`), giving
`∫_ℝ x^{2n} e^{-x²} = Γ(n + 1/2)`.  Feeding in `Real.Gamma_nat_add_half` produces
the double-factorial closed form.

The substitution step is exactly the one Mathlib uses to prove `Γ(1/2) = √π`,
generalised from the single exponent `1/2` to the whole ladder `n + 1/2`.

No new axioms: every step is a consequence of existing Mathlib results.
-/

open Real MeasureTheory Set
open scoped Nat

namespace AreaOfCircleOQ07OQ03OQ01

/-- **The half-integer Gamma ladder** (Mathlib re-export).
`Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ` for every natural `n`. -/
theorem gamma_nat_add_half (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) = ((2 * n - 1 : ℕ)‼ : ℝ) * Real.sqrt Real.pi / 2 ^ n :=
  Real.Gamma_nat_add_half n

/-- **Half-line even Gaussian moment.**
`∫_{x>0} x^{2n} e^{-x²} dx = Γ(n + 1/2) / 2`.

This is the `u = x²` substitution applied to Euler's integral for `Γ(n + 1/2)`,
the exact generalisation of Mathlib's proof of `Γ(1/2) = √π` to the whole ladder. -/
theorem gaussian_moment_Ioi (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2)) = Real.Gamma ((n : ℝ) + 1 / 2) / 2 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 / 2 := by positivity
  -- Euler's integral, then the substitution `u = x²`.
  have hGI : Real.Gamma ((n : ℝ) + 1 / 2)
      = 2 * ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2) := by
    rw [Real.Gamma_eq_integral hpos,
      ← integral_comp_rpow_Ioi_of_pos
        (g := fun y : ℝ => Real.exp (-y) * y ^ (((n : ℝ) + 1 / 2) - 1)) (zero_lt_two),
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    have hxle : (0 : ℝ) ≤ x := hx0.le
    have hx2 : x ^ (2 : ℝ) = x ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hcombine :
        x ^ ((2 : ℝ) - 1) * (x ^ (2 : ℝ)) ^ (((n : ℝ) + 1 / 2) - 1) = x ^ (2 * n) := by
      rw [← Real.rpow_mul hxle, ← Real.rpow_add hx0, ← Real.rpow_natCast x (2 * n)]
      congr 1
      push_cast
      ring
    calc
        (2 * x ^ ((2 : ℝ) - 1))
            • (Real.exp (-(x ^ (2 : ℝ))) * (x ^ (2 : ℝ)) ^ (((n : ℝ) + 1 / 2) - 1))
          = 2 * (x ^ ((2 : ℝ) - 1) * (x ^ (2 : ℝ)) ^ (((n : ℝ) + 1 / 2) - 1))
              * Real.exp (-(x ^ (2 : ℝ))) := by rw [smul_eq_mul]; ring
        _ = 2 * x ^ (2 * n) * Real.exp (-(x ^ 2)) := by rw [hcombine, hx2]
        _ = 2 * (x ^ (2 * n) * Real.exp (-x ^ 2)) := by ring
  rw [hGI]; ring

/-- **The even Gaussian moments are the half-integer Gamma values.**
`∫_ℝ x^{2n} e^{-x²} dx = Γ(n + 1/2)`.

The integrand is even, so the full line is twice the half line, which is
`Γ(n + 1/2)/2`. -/
theorem gaussian_even_moment (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2)) = Real.Gamma ((n : ℝ) + 1 / 2) := by
  -- replace the integrand by `|x|^{2n} e^{-|x|²}` (equal, since `2n` is even)
  have hcong : (∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2))
      = ∫ x : ℝ, |x| ^ (2 * n) * Real.exp (-|x| ^ 2) := by
    refine integral_congr_ae (ae_of_all _ (fun x => ?_))
    show x ^ (2 * n) * Real.exp (-x ^ 2) = |x| ^ (2 * n) * Real.exp (-|x| ^ 2)
    rw [(even_two_mul n).pow_abs, sq_abs]
  rw [hcong]
  -- fold to a half-line integral via evenness, then apply the moment formula
  have habs := integral_comp_abs (f := fun t : ℝ => t ^ (2 * n) * Real.exp (-t ^ 2))
  simp only at habs
  rw [habs, gaussian_moment_Ioi]
  ring

/-- **Closed form for the even Gaussian moments.**
`∫_ℝ x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2ⁿ`.

Combining the moment identity with the half-integer Gamma ladder. -/
theorem gaussian_even_moment_doubleFactorial (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2))
      = ((2 * n - 1 : ℕ)‼ : ℝ) * Real.sqrt Real.pi / 2 ^ n := by
  rw [gaussian_even_moment, gamma_nat_add_half]

/-- **The zeroth moment recovers the Gaussian integral** `∫_ℝ e^{-x²} = √π`,
the parent entry `area-of-circle-oq-07`. -/
theorem gaussian_even_moment_zero :
    (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
  have h := gaussian_even_moment 0
  simp only [Nat.mul_zero, pow_zero, one_mul, Nat.cast_zero, zero_add] at h
  rw [h, Real.Gamma_one_half_eq]

/-- **The second moment** `∫_ℝ x² e^{-x²} = √π / 2`, i.e. `Γ(3/2) = √π/2`. -/
theorem gaussian_even_moment_two :
    (∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2)) = Real.sqrt Real.pi / 2 := by
  have h := gaussian_even_moment 1
  simp only [Nat.mul_one, Nat.cast_one] at h
  have h2 := gamma_nat_add_half 1
  norm_num [Nat.doubleFactorial] at h2
  rw [h, show (1 : ℝ) + 1 / 2 = 3 / 2 by norm_num, h2]

end AreaOfCircleOQ07OQ03OQ01
