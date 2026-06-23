import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-
# The `n`-dimensional Gaussian integral: ∫_{ℝⁿ} e^{-b‖x‖²} = (π/b)^{n/2}

## Open Question (area-of-circle-oq-07-oq-04-oq-01-oq-01)
The parent `area-of-circle-oq-07-oq-04-oq-01` gives the genuinely two-dimensional Gaussian
area integral

    ∫_{ℝ²} e^{-b(x²+y²)} = π/b                              (Fubini + polar coordinates).

The two-dimensional polar trick is special to the plane.  This follow-up asks for the full
`n`-dimensional closed form, which the plane case is just the `n = 2` instance of:

    ∫_{ℝⁿ} e^{-b‖x‖²} = (π/b)^{n/2}                          (real `b > 0`).

## Answer: YES, for every dimension `n`, via finite-product Fubini.

The `n`-fold separability of the radial Gaussian is the engine: writing `x = (x₀,…,x_{n-1})`
and `‖x‖² = ∑ᵢ xᵢ²`, the integrand **factors over coordinates**,

    e^{-b ∑ᵢ xᵢ²} = ∏ᵢ e^{-b xᵢ²},

so Fubini for a finite product of σ-finite measures (`integral_fintype_prod_volume_eq_pow`)
turns the integral over `Fin n → ℝ` into the `n`-th power of the one-dimensional integral,
and Mathlib's closed form `∫_ℝ e^{-b x²} = √(π/b)` (`integral_gaussian`) finishes it:

    ∫_{ℝⁿ} e^{-b‖x‖²} = (∫_ℝ e^{-b x²})ⁿ = (√(π/b))ⁿ = (π/b)^{n/2}.

* `prod_gaussian_eq_exp_radial` — coordinate factorization `∏ᵢ e^{-b xᵢ²} = e^{-b ∑ᵢ xᵢ²}`.
* `gaussian_euclidean_eq_sqrt_pow` — Fubini + one-dimensional closed form: the integral
  equals `√(π/b)ⁿ`.  (Holds for every real `b`, since `integral_gaussian` does.)
* `gaussian_euclidean_eq_rpow` — the classical exponent form `(π/b)^{n/2}` (real `b > 0`),
  obtained from `√(π/b)ⁿ` by `√t = t^{1/2}` and `(t^{1/2})ⁿ = t^{n/2}`.
* `gaussian_euclidean_two` — the `n = 2` instance recovers the parent's planar value `π/b`,
  now as an integral over `Fin 2 → ℝ` rather than over `ℝ × ℝ`.
* `gaussian_euclidean_one` — the `n = 1` instance is exactly Mathlib's `√(π/b)`.

Mathlib has the one-dimensional Gaussian and a finite-product Fubini theorem, but not the
assembled `n`-dimensional closed form `(π/b)^{n/2}` for the real radial Gaussian; that
assembly (coordinate factorization, the `card (Fin n) = n` bookkeeping, and the
`√(π/b)ⁿ = (π/b)^{n/2}` exponent calculation) is carried out here.  No new axioms.
-/

open Real MeasureTheory Finset

namespace AreaOfCircleOQ07OQ04OQ01OQ01

variable {b : ℝ}

/-- **Coordinate factorization.** The `n`-fold product of one-dimensional Gaussians is the
radial Gaussian of the squared Euclidean norm `∑ᵢ xᵢ²`. -/
theorem prod_gaussian_eq_exp_radial {n : ℕ} (x : Fin n → ℝ) :
    ∏ i, Real.exp (-b * (x i) ^ 2) = Real.exp (-b * ∑ i, (x i) ^ 2) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- **Fubini + one-dimensional closed form.** The integral of the radial Gaussian over
`Fin n → ℝ` (carrying the product Lebesgue measure) is the `n`-th power of the
one-dimensional Gaussian integral, namely `√(π/b)ⁿ`.  Valid for every real `b`. -/
theorem gaussian_euclidean_eq_sqrt_pow {n : ℕ} (b : ℝ) :
    ∫ x : Fin n → ℝ, Real.exp (-b * ∑ i, (x i) ^ 2) = Real.sqrt (π / b) ^ n := by
  simp_rw [← prod_gaussian_eq_exp_radial]
  rw [integral_fintype_prod_volume_eq_pow (fun x : ℝ => Real.exp (-b * x ^ 2)),
      integral_gaussian, Fintype.card_fin]

/-- **The `n`-dimensional Gaussian closed form.** For `b > 0`,
`∫_{ℝⁿ} e^{-b‖x‖²} = (π/b)^{n/2}`. -/
theorem gaussian_euclidean_eq_rpow {n : ℕ} (hb : 0 < b) :
    ∫ x : Fin n → ℝ, Real.exp (-b * ∑ i, (x i) ^ 2) = (π / b) ^ ((n : ℝ) / 2) := by
  have hpos : 0 ≤ π / b := le_of_lt (div_pos pi_pos hb)
  rw [gaussian_euclidean_eq_sqrt_pow, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast ((π / b) ^ (1 / (2 : ℝ))) n, ← Real.rpow_mul hpos]
  congr 1
  ring

/-- **Plane case (`n = 2`).** Recovers the parent open question's value `π/b`, now realized
as an integral over `Fin 2 → ℝ` with the product measure. -/
theorem gaussian_euclidean_two (hb : 0 < b) :
    ∫ x : Fin 2 → ℝ, Real.exp (-b * ∑ i, (x i) ^ 2) = π / b := by
  rw [gaussian_euclidean_eq_sqrt_pow, Real.sq_sqrt (le_of_lt (div_pos pi_pos hb))]

/-- **Line case (`n = 1`).** Reduces to Mathlib's one-dimensional Gaussian value `√(π/b)`. -/
theorem gaussian_euclidean_one (b : ℝ) :
    ∫ x : Fin 1 → ℝ, Real.exp (-b * ∑ i, (x i) ^ 2) = Real.sqrt (π / b) := by
  rw [gaussian_euclidean_eq_sqrt_pow, pow_one]

end AreaOfCircleOQ07OQ04OQ01OQ01
