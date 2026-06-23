import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-
# The squared Gaussian integral as a literal 2-D area (Fubini/Tonelli)

## Open Question (area-of-circle-oq-07-oq-04-oq-01)
The parent `area-of-circle-oq-07-oq-04` proved
    (∫_ℝ e^{-b x²} dx)² = π / b
by *squaring* Mathlib's closed-form one-dimensional Gaussian value — a purely
algebraic step that hides the geometry.  This follow-up makes the geometry
explicit: it identifies the square with a genuine **two-dimensional integral**
over the plane,
    (∫_ℝ e^{-b x²} dx)² = ∫_{ℝ²} e^{-b (x² + y²)} d(x,y),
which is exactly the Fubini/Tonelli step that opens the classical
`(∫ e^{-x²})² = ∫∫ e^{-(x²+y²)} = π` polar-coordinates computation underlying the
whole `area-of-circle` Gaussian story.

## Answer: YES.

The integrand on the plane *separates*:
    e^{-b (x² + y²)} = e^{-b x²} · e^{-b y²},
so the planar integral is a product integral of a separable function.  Mathlib's
`MeasureTheory.integral_prod_mul` evaluates such an integral as the product of the
two one-dimensional integrals *unconditionally* (no integrability hypothesis is
needed — both sides degenerate consistently when a factor fails to be integrable):
    ∫_{ℝ²} f(x) g(y) d(x,y) = (∫ f) · (∫ g).
With `f = g = (e^{-b ·²})` the right-hand side is `(∫_ℝ e^{-b x²})²`.  The plane's
volume is the product measure (`Measure.volume_eq_prod`), so the planar Bochner
integral over `ℝ × ℝ` is literally the product integral.

Because `integral_prod_mul` carries no hypotheses, the area identity holds for
**every real `b`** — for `b ≤ 0` both sides are `0` (the integrand is not
integrable and Bochner integrals of non-integrable functions vanish).

Combining with Mathlib's closed form `integral_gaussian b : ∫ e^{-b x²} = √(π/b)`
recovers the planar value `π/b` for `0 < b`, closing the loop with the parent.

No new axioms: a separation of the exponential plus existing Mathlib results.
-/

open Real MeasureTheory

namespace AreaOfCircleOQ07OQ04OQ01

/-- **Separation of the planar Gaussian.** The two-dimensional Gaussian weight
factors into a product of one-dimensional weights:
`e^{-b (x² + y²)} = e^{-b x²} · e^{-b y²}`. -/
theorem exp_neg_mul_add_sq (b x y : ℝ) :
    Real.exp (-b * (x ^ 2 + y ^ 2))
      = Real.exp (-b * x ^ 2) * Real.exp (-b * y ^ 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- **The squared Gaussian integral as a literal 2-D area.** For every real `b`,
the square of the one-dimensional Gaussian integral equals the genuine planar
integral of the radial Gaussian weight `e^{-b (x² + y²)}` over `ℝ²`:
`(∫_ℝ e^{-b x²} dx)² = ∫_{ℝ²} e^{-b (x² + y²)} d(x,y)`.

This is the Fubini/Tonelli step that turns the algebraic "squaring" of the parent
`area-of-circle-oq-07-oq-04` into the two-dimensional area whose polar evaluation
gives `π/b`.  It holds unconditionally: for `b ≤ 0` both sides are `0`. -/
theorem gaussian_integral_sq_eq_integral_plane (b : ℝ) :
    (∫ x : ℝ, Real.exp (-b * x ^ 2)) ^ 2
      = ∫ p : ℝ × ℝ, Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)) := by
  -- Separate the radial weight into a product of one-dimensional weights.
  have hpt : (fun p : ℝ × ℝ => Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2)))
      = fun p : ℝ × ℝ => Real.exp (-b * p.1 ^ 2) * Real.exp (-b * p.2 ^ 2) :=
    funext fun p => exp_neg_mul_add_sq b p.1 p.2
  rw [hpt, pow_two]
  -- The plane's volume is the product measure (`volume_eq_prod`, definitionally),
  -- so the planar integral of the separated weight is the product integral.
  exact (integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun x : ℝ => Real.exp (-b * x ^ 2))
      (fun y : ℝ => Real.exp (-b * y ^ 2))).symm

/-- **The planar Gaussian integral has value `π/b`.** For `0 < b`, the literal
two-dimensional integral of `e^{-b (x² + y²)}` over `ℝ²` evaluates to `π/b`,
recovering the parent's rational value through the genuine area.  Together with
`gaussian_integral_sq_eq_integral_plane` this realizes
`(∫_ℝ e^{-b x²})² = ∫_{ℝ²} e^{-b(x²+y²)} = π/b`. -/
theorem integral_plane_gaussian_eq (b : ℝ) (hb : 0 < b) :
    (∫ p : ℝ × ℝ, Real.exp (-b * (p.1 ^ 2 + p.2 ^ 2))) = π / b := by
  rw [← gaussian_integral_sq_eq_integral_plane, integral_gaussian, Real.sq_sqrt]
  positivity

/-- The classical `b = 1` specialization: the unit-weight planar Gaussian has
area `π`, the two-dimensional form of `(∫_ℝ e^{-x²})² = π`. -/
theorem integral_plane_gaussian_one :
    (∫ p : ℝ × ℝ, Real.exp (-(1 : ℝ) * (p.1 ^ 2 + p.2 ^ 2))) = π := by
  rw [integral_plane_gaussian_eq 1 one_pos, div_one]

end AreaOfCircleOQ07OQ04OQ01
