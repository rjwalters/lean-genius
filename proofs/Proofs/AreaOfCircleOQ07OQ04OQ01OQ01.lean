import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-
# The `n`-dimensional Gaussian integral: ∫_{ℝⁿ} e^{-b ∑ xᵢ²} = (π/b)^{n/2}

## Open Question (area-of-circle-oq-07-oq-04-oq-01-oq-01)
The parent `area-of-circle-oq-07-oq-04-oq-01` realizes `π/b` as the **literal two-dimensional
area integral** of the radially symmetric Gaussian `e^{-b(x²+y²)}` over the plane, proving
`(∫_ℝ e^{-b x²})² = ∫_{ℝ²} e^{-b(x²+y²)} = π/b` via Fubini and polar coordinates.

The 2-D Fubini step there is the special case `n = 2` of a general product identity: the
`n`-dimensional Gaussian integral over `ℝⁿ` factors as the `n`-th power of the
one-dimensional line integral.  This follow-up proves that general dimension statement and
chains it with Mathlib's closed form `∫_ℝ e^{-b x²} = √(π/b)` to obtain the classical

    ∫_{ℝⁿ} e^{-b ∑ᵢ xᵢ²}  =  (∫_ℝ e^{-b x²})ⁿ  =  (π/b)^{n/2}.

Here `ℝⁿ` is `Fin n → ℝ` carried by the product (Lebesgue) measure, and `∑ᵢ xᵢ²` is the
squared Euclidean norm `‖x‖²`.

## Answer: YES.  (every `n : ℕ`; the closed form needs real `b > 0`)

* `gaussian_pow_eq_integral_pi` — the **product–Fubini step** in arbitrary dimension:
  `∫_{ℝⁿ} e^{-b ∑ᵢ xᵢ²} = (∫_ℝ e^{-b x²})ⁿ`, from `integral_fintype_prod_volume_eq_pow`
  after rewriting the radial integrand `e^{-b ∑ᵢ xᵢ²}` as the product `∏ᵢ e^{-b xᵢ²}`
  (`Real.exp_sum`).  No positivity hypothesis: this holds for every real `b`.
* `integral_pi_gaussian_eq_sqrt_pow` — substituting Mathlib's `integral_gaussian`:
  `∫_{ℝⁿ} e^{-b ∑ᵢ xᵢ²} = (√(π/b))ⁿ`, again for every real `b`.
* `integral_pi_gaussian_eq_rpow` — the standard closed form `(π/b)^{n/2}` (real exponent),
  valid for `b > 0` where `π/b ≥ 0` lets `√(π/b)ⁿ = (π/b)^{n/2}`.
* `integral_pi_gaussian_eq_pi` — the `b = 1` form `∫_{ℝⁿ} e^{-‖x‖²} = π^{n/2}`.

The `n = 1` case recovers Mathlib's base integral and the `n = 2` case recovers the parent's
2-D area identity; the engine is the `n`-fold Fubini factorization of the separable Gaussian.
No new axioms.
-/

open Real MeasureTheory Finset

namespace AreaOfCircleOQ07OQ04OQ01OQ01

variable {b : ℝ}

/-- **Product–Fubini step (arbitrary dimension).** The integral of the radially symmetric
Gaussian `e^{-b ∑ᵢ xᵢ²}` over `ℝⁿ = Fin n → ℝ` equals the `n`-th power of the one-dimensional
line integral `∫_ℝ e^{-b x²}`.  The separable integrand `e^{-b ∑ᵢ xᵢ²}` factors as the product
`∏ᵢ e^{-b xᵢ²}` (`Real.exp_sum`), and `integral_fintype_prod_volume_eq_pow` collapses the
product integral to a power.  Holds for *every* real `b` (no integrability/positivity needed). -/
theorem gaussian_pow_eq_integral_pi (n : ℕ) :
    (∫ x : Fin n → ℝ, Real.exp (-b * ∑ i, (x i) ^ 2))
      = (∫ t : ℝ, Real.exp (-b * t ^ 2)) ^ n := by
  have key : (∫ x : Fin n → ℝ, ∏ i, Real.exp (-b * (x i) ^ 2))
      = (∫ t : ℝ, Real.exp (-b * t ^ 2)) ^ n := by
    rw [integral_fintype_prod_volume_eq_pow (fun t : ℝ => Real.exp (-b * t ^ 2)),
      Fintype.card_fin]
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  rw [← Real.exp_sum, Finset.mul_sum]

/-- **Closed form via Mathlib's `integral_gaussian`.** `∫_{ℝⁿ} e^{-b ∑ᵢ xᵢ²} = (√(π/b))ⁿ`,
for every real `b`. -/
theorem integral_pi_gaussian_eq_sqrt_pow (n : ℕ) :
    (∫ x : Fin n → ℝ, Real.exp (-b * ∑ i, (x i) ^ 2)) = Real.sqrt (π / b) ^ n := by
  rw [gaussian_pow_eq_integral_pi, integral_gaussian]

/-- **The `n`-dimensional Gaussian integral in standard closed form.**
`∫_{ℝⁿ} e^{-b ∑ᵢ xᵢ²} = (π/b)^{n/2}` (real exponent `n/2`), for `b > 0`. -/
theorem integral_pi_gaussian_eq_rpow (n : ℕ) (hb : 0 < b) :
    (∫ x : Fin n → ℝ, Real.exp (-b * ∑ i, (x i) ^ 2)) = (π / b) ^ ((n : ℝ) / 2) := by
  have hpb : (0 : ℝ) ≤ π / b := by positivity
  rw [integral_pi_gaussian_eq_sqrt_pow, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast ((π / b) ^ (1 / (2 : ℝ))) n, ← Real.rpow_mul hpb]
  congr 1
  ring

/-- The `b = 1` form: `∫_{ℝⁿ} e^{-∑ᵢ xᵢ²} = π^{n/2}`, the radial Gaussian mass over `ℝⁿ`. -/
theorem integral_pi_gaussian_eq_pi (n : ℕ) :
    (∫ x : Fin n → ℝ, Real.exp (-(∑ i, (x i) ^ 2))) = π ^ ((n : ℝ) / 2) := by
  have h := integral_pi_gaussian_eq_rpow (b := 1) n one_pos
  simp only [div_one, neg_mul, one_mul] at h
  exact h

end AreaOfCircleOQ07OQ04OQ01OQ01
