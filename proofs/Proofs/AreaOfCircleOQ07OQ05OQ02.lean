import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import Proofs.AreaOfCircleOQ07OQ05

/-
# The Gaussian Second Moment as a Gamma Special Value  (area-of-circle-oq-07-oq-05-oq-02)

## Open Question (area-of-circle-oq-07-oq-05-oq-02)
"Recover `√π/2` as a value of Euler's Gamma function directly through the
substitution `u = x²` and Mathlib's `Real.Gamma`, identifying the second moment
of the Gaussian with a Gamma special value rather than computing it by parts."

## Answer

The parent entry `area-of-circle-oq-07-oq-05` evaluated the **second moment**
`∫_{-∞}^{∞} x² e^{-x²} dx = √π/2` by integration by parts.  This entry gives the
**Gamma-function reading** of the same value: the substitution `u = x²` turns the
Gaussian weight into Euler's integral and pins the second moment to the
half-integer Gamma value `Γ(3/2)`.

Two faces of the answer, exactly:

* the **half-line** second moment is `½·Γ(3/2)`:
  `∫_{0}^{∞} x² e^{-x²} dx = ½·Γ(3/2) = √π/4`;
* the **full-line** second moment is `Γ(3/2)` itself:
  `∫_{-∞}^{∞} x² e^{-x²} dx = Γ(3/2) = √π/2`.

The `½` is not an accident: Euler's integral `Γ(s) = ∫_{0}^{∞} e^{-u} u^{s-1} du`
lives on the half-line, so the natural object the substitution produces is the
half-line moment `½·Γ(3/2)`; doubling by even symmetry recovers the parent's
full-line value.

## The substitution

For the half-line, write `Γ(3/2) = ∫_{0}^{∞} e^{-u} u^{1/2} du`
(`Real.Gamma_eq_integral`).  Mathlib's change-of-variables
`integral_comp_rpow_Ioi_of_pos` for `p = 2` is exactly the map `u = x²`:

  `∫_{0}^{∞} (2·x^{2-1})·g(x²) dx = ∫_{0}^{∞} g(u) du`.

With `g(u) = e^{-u} u^{1/2}` the left integrand is, for `x > 0`,
`2x · (e^{-x²}·x) = 2·x² e^{-x²}`, so `Γ(3/2) = 2·∫_{0}^{∞} x² e^{-x²} dx`, i.e.
`∫_{0}^{∞} x² e^{-x²} dx = ½·Γ(3/2)`.  This is the very substitution Mathlib uses
to prove `Γ(1/2) = √π`; here it is carried one half-power higher to land on
`Γ(3/2)` and the Gaussian *second* moment.

The special value `Γ(3/2) = √π/2` is `Γ(1/2 + 1) = ½·Γ(1/2) = ½·√π`
(`Real.Gamma_add_one`, `Real.Gamma_one_half_eq`).

No new axioms: every step is a routine consequence of existing Mathlib results
together with the parent's full-line value.
-/

open Real MeasureTheory Filter Topology Set

namespace AreaOfCircleOQ07OQ05OQ02

/-- **The half-integer Gamma special value `Γ(3/2) = √π/2`.**
Obtained from the functional equation `Γ(s+1) = s·Γ(s)` at `s = 1/2` together with
`Γ(1/2) = √π`: `Γ(3/2) = ½·Γ(1/2) = ½·√π`. -/
theorem Gamma_three_half : Real.Gamma (3 / 2) = Real.sqrt π / 2 := by
  have h : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
  rw [h, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

/-- **Euler integral representation of `Γ(3/2)`.**
`Γ(3/2) = ∫_{0}^{∞} e^{-x} x^{1/2} dx`, the `s = 3/2` instance of Euler's integral
`Γ(s) = ∫_{0}^{∞} e^{-x} x^{s-1} dx`. This is the half-line integral the `u = x²`
substitution acts on. -/
theorem Gamma_three_half_integral :
    Real.Gamma (3 / 2) = ∫ x in Ioi (0 : ℝ), Real.exp (-x) * x ^ (1 / 2 : ℝ) := by
  rw [Real.Gamma_eq_integral (by norm_num : (0 : ℝ) < 3 / 2)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  rw [show ((3 : ℝ) / 2 - 1) = (1 / 2 : ℝ) by norm_num]

/-- **The half-line second moment is `½·Γ(3/2)`, via the substitution `u = x²`.**
`∫_{0}^{∞} x² e^{-x²} dx = ½·Γ(3/2)`.  Applying Mathlib's change-of-variables
`integral_comp_rpow_Ioi_of_pos` (with `p = 2`, i.e. `u = x²`) to Euler's integral
for `Γ(3/2)` turns the integrand `e^{-u} u^{1/2}` into `2·x² e^{-x²}` on the
half-line, so `Γ(3/2) = 2·∫_{0}^{∞} x² e^{-x²} dx`. This is the higher-power analogue
of the substitution Mathlib uses for `Γ(1/2) = √π`. -/
theorem half_line_second_moment_eq_half_Gamma :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2) = (1 / 2) * Real.Gamma (3 / 2) := by
  have key : Real.Gamma (3 / 2)
      = 2 * ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2) := by
    rw [Gamma_three_half_integral,
      ← integral_comp_rpow_Ioi_of_pos
        (g := fun y => Real.exp (-y) * y ^ (1 / 2 : ℝ)) zero_lt_two,
      ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hxpos : (0 : ℝ) < x := hx
    have e2 : x ^ (2 : ℝ) = x ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have e3 : (x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = x := by
      rw [← Real.rpow_mul hxpos.le, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    simp only [smul_eq_mul]
    rw [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.rpow_one, e3, e2]
    ring
  rw [key]; ring

/-- **The half-line second moment in closed form: `√π/4`.**
Combining `half_line_second_moment_eq_half_Gamma` with `Γ(3/2) = √π/2`. -/
theorem half_line_second_moment_value :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2) = Real.sqrt π / 4 := by
  rw [half_line_second_moment_eq_half_Gamma, Gamma_three_half]; ring

/-- **The full-line second moment is the Gamma special value `Γ(3/2)`.**
Starting from the parent's full-line value `∫_ℝ x² e^{-x²} = √π/2` and the special
value `Γ(3/2) = √π/2`, the second moment is identified with a value of the Gamma
function — the answer to the open question. -/
theorem full_line_second_moment_eq_Gamma :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2) = Real.Gamma (3 / 2) := by
  rw [AreaOfCircleOQ07OQ05.gaussian_second_moment, Gamma_three_half]

/-- **Even symmetry: the full-line moment is twice the half-line moment.**
`∫_ℝ x² e^{-x²} = 2·∫_{0}^{∞} x² e^{-x²}` — equivalently `Γ(3/2) = 2·(½·Γ(3/2))`,
the bookkeeping that turns the half-line `½·Γ(3/2)` produced by Euler's integral
into the parent's full-line `Γ(3/2) = √π/2`. -/
theorem full_line_eq_two_mul_half_line :
    ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2)
      = 2 * ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x ^ 2) := by
  rw [full_line_second_moment_eq_Gamma, half_line_second_moment_eq_half_Gamma]; ring

end AreaOfCircleOQ07OQ05OQ02
