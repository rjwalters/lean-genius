import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

/-
# The half-integer Gamma ladder as the tower of even Gaussian moments

## Open Question (area-of-circle-oq-07-oq-03-oq-01)
Formalize the half-integer ladder `Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ` and identify
each value with the even Gaussian moment `∫_ℝ x^{2n} e^{-x²} dx`, extending the
single `√π` of the parent entry (`Γ(1/2) = √π`, the `n = 0` rung) to the whole
tower of half-integer Gamma values.

## Answer: YES — the even moments *are* the half-integer Gamma values.

The parent entry `area-of-circle-oq-07-oq-03` proves the bottom rung
`Γ(1/2) = √π = ∫_ℝ e^{-x²}`.  Here we climb the whole ladder.

The bridge is a single Mathlib evaluation, `integral_rpow_mul_exp_neg_rpow`,
which gives over the half-line `∫_{x>0} x^q e^{-x^p} = (1/p)·Γ((q+1)/p)`.
Specialising `p = 2`, `q = 2n` yields `∫_{x>0} x^{2n} e^{-x²} = ½·Γ(n + 1/2)`.
The integrand `x^{2n} e^{-x²}` is **even** (the exponent `2n` is even and
`e^{-x²}` depends only on `|x|`), so `integral_comp_abs` doubles the half-line
integral to the full line:

    ∫_ℝ x^{2n} e^{-x²} dx = 2 · ½ · Γ(n + 1/2) = Γ(n + 1/2).

Combined with Mathlib's closed form `Real.Gamma_nat_add_half`
(`Γ(k + 1/2) = (2k-1)‼ · √π / 2ᵏ`) this exhibits every even Gaussian moment as a
double-factorial multiple of `√π`:

    ∫_ℝ x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2ⁿ.

The companion odd moments vanish by oddness, so the *entire* moment sequence of
the Gaussian weight `e^{-x²}` is pinned down.

## Results
* `evenGaussianMoment_eq_gamma` — `∫_ℝ x^{2n} e^{-x²} = Γ(n + 1/2)`;
* `evenGaussianMoment_eq_doubleFactorial` — `∫_ℝ x^{2n} e^{-x²} = (2n-1)‼·√π/2ⁿ`;
* `gammaLadder` — re-export of the half-integer ladder `Γ(n+1/2) = (2n-1)‼·√π/2ⁿ`;
* `oddGaussianMoment_eq_zero` — `∫_ℝ x^{2n+1} e^{-x²} = 0`;
* `evenGaussianMoment_zero` — the `n = 0` rung recovers the parent `∫_ℝ e^{-x²} = √π`.

No new axioms: every step is a consequence of existing Mathlib results.
-/

open Real MeasureTheory Set
open scoped Nat

namespace AreaOfCircleOQ07OQ03OQ01

/-- **Half-line even moment.** `∫_{x>0} x^{2n} e^{-x²} = ½·Γ(n + 1/2)`.
The natural-power integrand is converted to the real-power form and evaluated by
Mathlib's `integral_rpow_mul_exp_neg_rpow` at `p = 2`, `q = 2n`. -/
private lemma halfLine_evenMoment (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2) = (1 / 2) * Real.Gamma (n + 1 / 2) := by
  rw [show (∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2))
        = ∫ x in Ioi (0 : ℝ), x ^ (2 * (n : ℝ)) * Real.exp (-x ^ (2 : ℝ)) from
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by
        rw [← Real.rpow_natCast x (2 * n), ← Real.rpow_natCast x 2]
        push_cast
        ring_nf)]
  rw [integral_rpow_mul_exp_neg_rpow (by norm_num : (0 : ℝ) < 2)
      (by have h : (0 : ℝ) ≤ 2 * (n : ℝ) := by positivity
          linarith)]
  rw [show (2 * (n : ℝ) + 1) / 2 = (n : ℝ) + 1 / 2 by ring]

/-- **Even Gaussian moment as a half-integer Gamma value.**
The `2n`-th moment of the Gaussian weight `e^{-x²}` over the whole real line is
exactly `Γ(n + 1/2)`.  The proof folds the line onto the half-line by evenness
(`integral_comp_abs`) and evaluates the half-line integral via
`halfLine_evenMoment`. -/
theorem evenGaussianMoment_eq_gamma (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) = Real.Gamma (n + 1 / 2) := by
  have heq : (fun x : ℝ => x ^ (2 * n) * Real.exp (-x ^ 2))
      = fun x : ℝ => (fun t : ℝ => t ^ (2 * n) * Real.exp (-t ^ 2)) |x| := by
    funext x
    simp only [sq_abs, (even_two_mul n).pow_abs]
  rw [heq, integral_comp_abs (f := fun t : ℝ => t ^ (2 * n) * Real.exp (-t ^ 2))]
  show 2 * (∫ x in Ioi (0 : ℝ), x ^ (2 * n) * Real.exp (-x ^ 2)) = Real.Gamma (n + 1 / 2)
  rw [halfLine_evenMoment]
  ring

/-- **The even Gaussian moments are double-factorial multiples of `√π`.**
`∫_ℝ x^{2n} e^{-x²} dx = (2n-1)‼ · √π / 2ⁿ`.  Combines the Gamma identification
above with Mathlib's closed form `Real.Gamma_nat_add_half`. -/
theorem evenGaussianMoment_eq_doubleFactorial (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n) * Real.exp (-x ^ 2) = (2 * n - 1)‼ * √π / 2 ^ n := by
  rw [evenGaussianMoment_eq_gamma, Real.Gamma_nat_add_half]

/-- **The half-integer Gamma ladder** (re-export of `Real.Gamma_nat_add_half`):
`Γ(n + 1/2) = (2n-1)‼ · √π / 2ⁿ`.  The whole tower above the parent entry's
`Γ(1/2) = √π` rung. -/
theorem gammaLadder (n : ℕ) :
    Real.Gamma (n + 1 / 2) = (2 * n - 1)‼ * √π / 2 ^ n :=
  Real.Gamma_nat_add_half n

/-- **The odd Gaussian moments vanish.**
`∫_ℝ x^{2n+1} e^{-x²} dx = 0`, because the integrand is an odd function and the
Lebesgue measure on `ℝ` is invariant under negation. -/
theorem oddGaussianMoment_eq_zero (n : ℕ) :
    ∫ x : ℝ, x ^ (2 * n + 1) * Real.exp (-x ^ 2) = 0 := by
  have hmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    measurableEmbedding_neg
    (fun x : ℝ => x ^ (2 * n + 1) * Real.exp (-x ^ 2))
  simp only [neg_sq, Odd.neg_pow (odd_two_mul_add_one n), neg_mul] at hmp
  rw [integral_neg] at hmp
  linarith

/-- **Bottom rung = parent entry.**  The `n = 0` even moment recovers the parent
entry's Gaussian integral `∫_ℝ e^{-x²} = √π` and the value `Γ(1/2)`. -/
theorem evenGaussianMoment_zero :
    ∫ x : ℝ, Real.exp (-x ^ 2) = √π := by
  have h := evenGaussianMoment_eq_gamma 0
  simp only [mul_zero, pow_zero, one_mul, Nat.cast_zero, zero_add] at h
  rw [h]
  exact Real.Gamma_one_half_eq

end AreaOfCircleOQ07OQ03OQ01
