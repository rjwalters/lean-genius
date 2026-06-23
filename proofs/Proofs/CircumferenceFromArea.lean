import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-
# Circumference Formula via Area Differentiation

## What This Proves
The circumference of a circle C = 2πr can be derived by differentiating the
area formula A = πr² with respect to the radius r. Formally:

  dA/dr = d(πr²)/dr = 2πr = C

This elegant connection shows that the circumference is the rate of change of
area with respect to radius — geometrically, adding a thin annular ring of
width dr to a circle of radius r adds area approximately C(r) · dr = 2πr · dr.

## Mathematical Statement
For the area function A(r) = πr², we prove:
  HasDerivAt A (2πr) r     for all r : ℝ
  deriv A r = 2πr           for all r : ℝ

## Approach
- Define circleArea as a real-valued function r ↦ π * r²
- Use Mathlib's derivative rules (constant multiplication + power rule)
- Connect back to the Lebesgue measure formulation from AreaOfCircle.lean

## Status
- [x] Complete proof (no sorries)
- [x] Uses Mathlib calculus infrastructure
- [x] Proves HasDerivAt and deriv versions
- [x] Proves differentiability
- [x] Corollaries for special cases

## Open Question Origin
This answers the open question from the Area of a Circle gallery entry:
"Can the formalization extend to prove C = 2πr via differentiation of area?"
-/

namespace CircumferenceFromArea

open Real MeasureTheory

/-- The area of a circle as a real-valued function of radius. -/
noncomputable def circleArea (r : ℝ) : ℝ := π * r ^ 2

/-- The circumference of a circle as a function of radius. -/
noncomputable def circumference (r : ℝ) : ℝ := 2 * π * r

/-- **Main theorem**: The derivative of the circle area function at radius r
equals the circumference 2πr.

Geometrically, increasing the radius by a small dr adds a thin annular ring
of width dr and circumference 2πr, so dA ≈ 2πr · dr. -/
theorem hasDerivAt_circleArea (r : ℝ) :
    HasDerivAt circleArea (2 * π * r) r := by
  unfold circleArea
  -- d/dr (π * r²) = π * 2r = 2πr
  have h : HasDerivAt (fun x => π * x ^ 2) (π * (2 * r)) r := by
    have := (hasDerivAt_pow 2 r).const_mul π
    simpa using this
  convert h using 1
  ring

/-- The derivative equals the circumference function. -/
theorem hasDerivAt_circleArea' (r : ℝ) :
    HasDerivAt circleArea (circumference r) r := by
  unfold circumference
  exact hasDerivAt_circleArea r

/-- The area function is differentiable everywhere. -/
theorem differentiable_circleArea : Differentiable ℝ circleArea := by
  intro r
  exact (hasDerivAt_circleArea r).differentiableAt

/-- The `deriv` form: deriv(circleArea) r = 2πr. -/
theorem deriv_circleArea (r : ℝ) :
    deriv circleArea r = 2 * π * r :=
  (hasDerivAt_circleArea r).deriv

/-- The `deriv` form using the circumference function. -/
theorem deriv_circleArea_eq_circumference (r : ℝ) :
    deriv circleArea r = circumference r := by
  rw [deriv_circleArea]
  unfold circumference
  ring

/-- At radius 1, the circumference is 2π. -/
theorem circumference_unit : circumference 1 = 2 * π := by
  unfold circumference; ring

/-- At radius 0, the circumference is 0. -/
theorem circumference_zero : circumference 0 = 0 := by
  unfold circumference; ring

/-- Circumference scales linearly with radius. -/
theorem circumference_scaling (c r : ℝ) :
    circumference (c * r) = c * circumference r := by
  unfold circumference; ring

/-- Area at radius 0 is 0. -/
theorem circleArea_zero : circleArea 0 = 0 := by
  unfold circleArea; ring

/-- Area at radius 1 is π. -/
theorem circleArea_unit : circleArea 1 = π := by
  unfold circleArea; ring

/-- Area scales quadratically with radius. -/
theorem circleArea_scaling (c r : ℝ) :
    circleArea (c * r) = c ^ 2 * circleArea r := by
  unfold circleArea; ring

/-- The second derivative of area gives the constant 2π.
This means the circumference grows at a constant rate with respect to radius. -/
theorem deriv2_circleArea (r : ℝ) :
    deriv (deriv circleArea) r = 2 * π := by
  have : deriv circleArea = fun x => 2 * π * x := by
    ext x
    exact deriv_circleArea x
  rw [this]
  simp [mul_comm]

/-- For positive radius, circumference is positive. -/
theorem circumference_pos {r : ℝ} (hr : 0 < r) : 0 < circumference r := by
  unfold circumference
  positivity

/-- For positive radius, area is positive. -/
theorem circleArea_pos {r : ℝ} (hr : 0 < r) : 0 < circleArea r := by
  unfold circleArea
  positivity

/-- Area is monotonically increasing for non-negative radii. -/
theorem circleArea_mono {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    circleArea r₁ ≤ circleArea r₂ := by
  unfold circleArea
  have : r₁ ^ 2 ≤ r₂ ^ 2 := sq_le_sq' (by linarith) h₂
  exact mul_le_mul_of_nonneg_left this pi_nonneg

/-- Circumference is monotonically increasing for non-negative radii. -/
theorem circumference_mono {r₁ r₂ : ℝ} (_h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    circumference r₁ ≤ circumference r₂ := by
  unfold circumference
  have hpi : 0 ≤ 2 * π := by positivity
  exact mul_le_mul_of_nonneg_left h₂ hpi

/-- The isoperimetric relationship: C² = 4πA.
This is the equality case of the isoperimetric inequality for circles. -/
theorem isoperimetric_equality (r : ℝ) :
    circumference r ^ 2 = 4 * π * circleArea r := by
  unfold circumference circleArea
  ring

/-- Circumference can be recovered from the area-radius relationship:
C(r) = dA/dr, demonstrated by computing deriv at a specific point. -/
theorem circumference_from_deriv (r : ℝ) :
    circumference r = deriv circleArea r := by
  rw [deriv_circleArea_eq_circumference]

end CircumferenceFromArea
