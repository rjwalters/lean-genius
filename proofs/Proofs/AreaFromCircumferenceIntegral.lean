import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.FundThmCalculus
import Mathlib.Tactic

/-
# Area from Circumference Integration

## What This Proves
The area of a circle A = πr² can be derived by integrating the circumference
formula C(ρ) = 2πρ from 0 to r:

  A(r) = ∫₀ʳ C(ρ) dρ = ∫₀ʳ 2πρ dρ = πr²

This formalizes the geometric picture attributed to Archimedes: the disk is
composed of infinitely many thin concentric rings (annuli). Each ring at
radius ρ has circumference 2πρ and width dρ, contributing area 2πρ dρ.
Summing (integrating) from ρ = 0 to ρ = r recovers the full disk area πr².

## Mathematical Statement
For the area function A(r) = πr² and circumference C(ρ) = 2πρ, we prove:

  ∫ ρ in 0..r, C(ρ) dρ = A(r)   for all r : ℝ

This is the converse direction to the differentiation formula dA/dr = C(r),
together forming a complete picture of the duality between area and circumference
via the Fundamental Theorem of Calculus.

## Approach
- Define circleArea(r) = πr² and circumference(ρ) = 2πρ
- Show HasDerivAt circleArea (circumference r) r (power rule + constant multiply)
- Apply FTC Part 2 (integral_eq_sub_of_hasDerivAt):
    ∫ ρ in 0..r, circumference ρ = circleArea r - circleArea 0 = πr² - 0 = πr²
- The circumference function is continuous, hence integrable on any interval

## Status
- [x] Complete proof (no sorries)
- [x] Uses FTC Part 2 from Mathlib
- [x] Proves the formula for all r : ℝ (including r < 0 via signed integrals)
- [x] Corollaries: direct computation verification, annulus formula

## Open Question Origin
This answers the open question from the Circumference from Area gallery entry:
"Can the integral direction be formalized: A(r) = ∫₀ʳ C(ρ) dρ?"
-/

namespace AreaFromCircumferenceIntegral

open Real MeasureTheory intervalIntegral Topology

/-- The area of a circle as a real-valued function of radius. -/
noncomputable def circleArea (r : ℝ) : ℝ := π * r ^ 2

/-- The circumference of a circle as a function of radius. -/
noncomputable def circumference (r : ℝ) : ℝ := 2 * π * r

/-- The derivative of the circle area function at radius r equals the circumference 2πr.
This is the key link: area and circumference are related by differentiation. -/
theorem hasDerivAt_circleArea (r : ℝ) :
    HasDerivAt circleArea (circumference r) r := by
  unfold circleArea circumference
  have h : HasDerivAt (fun x => π * x ^ 2) (π * (2 * r)) r :=
    (hasDerivAt_pow 2 r).const_mul π |> (by simpa using ·)
  convert h using 1
  ring

/-- The area function is continuous. -/
theorem continuous_circleArea : Continuous circleArea := by
  unfold circleArea
  continuity

/-- The circumference function is continuous. -/
theorem continuous_circumference : Continuous circumference := by
  unfold circumference
  continuity

/-- **Main Theorem**: Integrating the circumference from 0 to r recovers the area.
  ∫₀ʳ C(ρ) dρ = A(r)
This is the FTC-based formalization of Archimedes' "sum of rings" argument. -/
theorem area_from_integral (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, circumference ρ = circleArea r := by
  -- FTC Part 2: ∫₀ʳ F'(ρ) dρ = F(r) - F(0) when F' = circumference
  have h_deriv : ∀ x ∈ Set.uIcc (0 : ℝ) r, HasDerivAt circleArea (circumference x) x :=
    fun x _ => hasDerivAt_circleArea x
  have h_int : IntervalIntegrable circumference volume 0 r :=
    continuous_circumference.intervalIntegrable 0 r
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int]
  -- Simplify: circleArea r - circleArea 0 = πr² - 0 = πr²
  simp [circleArea]

/-- Direct computation: ∫₀ʳ 2πρ dρ = πr².
Unfolds the definitions to show the raw integral formula. -/
theorem area_from_integral_explicit (r : ℝ) :
    ∫ ρ in (0 : ℝ)..r, 2 * π * ρ = π * r ^ 2 := by
  have := area_from_integral r
  simp only [circumference, circleArea] at this
  exact this

/-- The area difference between radii r₁ and r₂ equals the integral of circumference
over [r₁, r₂]. This generalizes the area formula to arbitrary annuli. -/
theorem annulus_area_from_integral (r₁ r₂ : ℝ) :
    ∫ ρ in r₁..r₂, circumference ρ = circleArea r₂ - circleArea r₁ := by
  have h_deriv : ∀ x ∈ Set.uIcc r₁ r₂, HasDerivAt circleArea (circumference x) x :=
    fun x _ => hasDerivAt_circleArea x
  have h_int : IntervalIntegrable circumference volume r₁ r₂ :=
    continuous_circumference.intervalIntegrable r₁ r₂
  rw [integral_eq_sub_of_hasDerivAt h_deriv h_int]

/-- The annulus between radii r₁ and r₂ has area ∫_{r₁}^{r₂} 2πρ dρ = π(r₂² - r₁²). -/
theorem annulus_area_formula (r₁ r₂ : ℝ) :
    ∫ ρ in r₁..r₂, circumference ρ = π * (r₂ ^ 2 - r₁ ^ 2) := by
  rw [annulus_area_from_integral]
  unfold circleArea
  ring

/-- The area formula is consistent: differentiating the integral recovers the circumference.
This closes the circle (pun intended): ∫↑ gives A, d/dr gives C = 2πr. -/
theorem diff_area_eq_circumference (r : ℝ) :
    HasDerivAt (fun s => ∫ ρ in (0 : ℝ)..s, circumference ρ) (circumference r) r := by
  -- The derivative of (∫₀ˢ C(ρ) dρ) w.r.t. s is C(s) by FTC Part 1
  exact integral_hasDerivAt_right
    (continuous_circumference.intervalIntegrable 0 r)
    (continuous_circumference.stronglyMeasurableAtFilter volume (𝓝 r))
    continuous_circumference.continuousAt

/-- At radius 1, the integral of circumference from 0 to 1 equals π (the unit disk area). -/
theorem unit_disk_area : ∫ ρ in (0 : ℝ)..1, circumference ρ = π := by
  have := area_from_integral 1
  simp [circumference, circleArea] at this ⊢
  linarith

/-- Scaling: multiplying the radius by c scales the area by c². -/
theorem area_scaling (c r : ℝ) :
    ∫ ρ in (0 : ℝ)..c * r, circumference ρ = c ^ 2 * circleArea r := by
  rw [area_from_integral]
  unfold circleArea
  ring

end AreaFromCircumferenceIntegral
