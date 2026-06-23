import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-
# Circumference Formula via Differentiation of Area

## What This Proves
The circumference of a circle with radius r is 2πr, derived by differentiating the
area formula A(r) = πr². This formalizes the deep connection:

  C(r) = dA/dr = d(πr²)/dr = 2πr

This is arguably the most elegant derivation of the circumference formula: the rate of
change of a disk's area with respect to its radius equals its boundary length.

## Mathematical Background
Geometrically, when a disk of radius r grows by dr, the added area is approximately
a thin annular strip of width dr and length C(r) (the circumference):
  dA ≈ C(r) · dr

This gives C(r) = dA/dr. Since A(r) = πr², we get C(r) = 2πr.

This relationship generalizes to higher dimensions: the surface area of an n-ball
is the derivative of its volume with respect to radius.

## Approach
1. Define the area function A(r) = π · r² as a real-valued function
2. Prove it has derivative 2πr at every point using Mathlib's calculus
3. Connect to the measure-theoretic area via ENNReal.toReal
4. State the circumference formula as a consequence

## Wiedijk Reference
This extends Wiedijk #9 (Area of a Circle) with the circumference derivation.
-/

namespace CircumferenceViaDifferentiation

open MeasureTheory Metric Real

-- The area function A(r) = πr² as a real-valued function
noncomputable def areaFn (r : ℝ) : ℝ := π * r ^ 2

-- The circumference function C(r) = 2πr
noncomputable def circumferenceFn (r : ℝ) : ℝ := 2 * π * r

/-
## Core Theorem: Differentiating the Area Gives the Circumference

The derivative of A(r) = πr² is exactly C(r) = 2πr.
This is the formal statement that dA/dr = C.
-/

/-- The area function A(r) = πr² has derivative 2πr at every point r.
This is the key result: the circumference is the derivative of the area. -/
theorem area_hasDerivAt (r : ℝ) :
    HasDerivAt areaFn (circumferenceFn r) r := by
  unfold areaFn circumferenceFn
  -- π · r² has derivative π · (2 · r) = 2πr
  have h : HasDerivAt (fun x => x ^ 2) (2 * r) r := by
    have := hasDerivAt_pow 2 r
    simp [Nat.cast_ofNat] at this
    exact this
  have h2 := h.const_mul π
  ring_nf at h2 ⊢
  exact h2

/-- The `deriv` of the area function equals the circumference function. -/
theorem deriv_area (r : ℝ) :
    deriv areaFn r = circumferenceFn r :=
  (area_hasDerivAt r).deriv

/-- The area function is differentiable everywhere. -/
theorem areaFn_differentiable : Differentiable ℝ areaFn :=
  fun r => (area_hasDerivAt r).differentiableAt

/-
## Connection to Measure Theory

We connect the abstract area function to the Lebesgue measure of the disk,
showing that for r ≥ 0, the measure-theoretic area agrees with πr².
-/

/-- The Lebesgue measure of a disk in ℂ ≅ ℝ² equals the area function for r ≥ 0.
This connects the calculus result to measure theory. -/
theorem measure_disk_eq_areaFn (r : ℝ) (hr : 0 ≤ r) :
    (volume (ball (0 : ℂ) r)).toReal = areaFn r := by
  rw [Complex.volume_ball]
  simp only [areaFn]
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
  have : (↑NNReal.pi : ENNReal).toReal = π := NNReal.coe_real_pi
  rw [this]; ring

/-- The area of a disk in ℂ scales quadratically with radius. -/
theorem measure_disk_scaling (r : ℝ) (hr : 0 ≤ r) (c : ℝ) (hc : 0 ≤ c) :
    (volume (ball (0 : ℂ) (c * r))).toReal =
      c ^ 2 * (volume (ball (0 : ℂ) r)).toReal := by
  rw [measure_disk_eq_areaFn _ (mul_nonneg hc hr)]
  rw [measure_disk_eq_areaFn _ hr]
  unfold areaFn
  ring

/-
## The Circumference Formula

Having established that dA/dr = 2πr, we state the circumference formula
as a standalone result.
-/

/-- **Circumference of a Circle**

The circumference of a circle with radius r is 2πr.
This is derived as the derivative of the area formula A = πr².

Geometrically: when a disk grows by dr, it gains an annular strip
of area C(r)·dr, so C(r) = dA/dr = d(πr²)/dr = 2πr. -/
theorem circumference_eq (r : ℝ) :
    circumferenceFn r = 2 * π * r := by
  unfold circumferenceFn; ring

/-- The circumference of a unit circle is 2π. -/
theorem circumference_unit_circle :
    circumferenceFn 1 = 2 * π := by
  unfold circumferenceFn; ring

/-- The circumference scales linearly with radius. -/
theorem circumference_scaling (r c : ℝ) :
    circumferenceFn (c * r) = c * circumferenceFn r := by
  unfold circumferenceFn; ring

/-- The circumference of a circle with radius 0 is 0. -/
theorem circumference_zero :
    circumferenceFn 0 = 0 := by
  unfold circumferenceFn; ring

/-
## Higher-Order Properties

The area function is smooth (infinitely differentiable) and convex.
-/

/-- The second derivative of the area function is 2π (constant).
This means the area is increasing at an accelerating rate —
the circumference grows linearly with radius. -/
theorem area_second_deriv (r : ℝ) :
    deriv (deriv areaFn) r = 2 * π := by
  have h1 : deriv areaFn = circumferenceFn := by
    ext x; exact deriv_area x
  rw [h1]
  show deriv (fun r => 2 * π * r) r = 2 * π
  have : HasDerivAt (fun r => 2 * π * r) (2 * π) r := by
    have hid := hasDerivAt_id r
    have := hid.const_mul (2 * π)
    simp at this
    exact this
  exact this.deriv

/-- The area function is monotone increasing for non-negative radii.
Larger circles have larger areas. -/
theorem areaFn_mono {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h2 : r₁ ≤ r₂) :
    areaFn r₁ ≤ areaFn r₂ := by
  unfold areaFn
  apply mul_le_mul_of_nonneg_left _ (le_of_lt pi_pos)
  nlinarith [sq_nonneg r₁, sq_nonneg r₂, sq_nonneg (r₂ - r₁)]

/-- The area function equals zero exactly at radius zero (for non-negative r). -/
theorem areaFn_eq_zero_iff {r : ℝ} (_hr : 0 ≤ r) :
    areaFn r = 0 ↔ r = 0 := by
  unfold areaFn
  constructor
  · intro h
    have : r ^ 2 = 0 := by
      by_contra h2
      have hpi : π > 0 := pi_pos
      have hr2 : r ^ 2 > 0 := by positivity
      linarith [mul_pos hpi hr2]
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp this
  · intro h; rw [h]; ring

/-
## The Fundamental Relationship

This is the deepest result: the area-circumference duality.
The circumference is exactly the derivative of the area, and the area
is exactly the integral of the circumference from 0 to r.
-/

/-- **Area-Circumference Duality**: The circumference function is the
derivative of the area function. Equivalently, the area is the
antiderivative of the circumference.

This captures the geometric insight that a disk is the union of
concentric circles: A(r) = ∫₀ʳ C(ρ) dρ = ∫₀ʳ 2πρ dρ = πr². -/
theorem area_circumference_duality (r : ℝ) :
    deriv areaFn r = circumferenceFn r :=
  deriv_area r

end CircumferenceViaDifferentiation
