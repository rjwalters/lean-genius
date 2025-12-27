import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Area of a Circle

## What This Proves
The area of a circle (or disk) with radius r is πr². More precisely, we prove that the
Lebesgue measure (area) of a 2-dimensional ball equals π times the square of its radius.

**Wiedijk Reference**: https://www.cs.ru.nl/~freek/100/ (#9)

## Mathematical Statement

For a disk D = {p ∈ ℝ² : |p - center| ≤ r} with radius r ≥ 0:
  Area(D) = πr²

This is one of the most fundamental formulas in geometry, known since antiquity.
Archimedes proved it around 250 BCE using the method of exhaustion.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's volume theorems which compute the
  Lebesgue measure of balls in Euclidean spaces.
- **Primary result:** We use `Complex.volume_ball` since ℂ ≅ ℝ² as a real vector space,
  and this gives the cleanest form of πr².
- **Key Insight:** In measure theory, "area" is formalized as Lebesgue measure in ℝ².
  The volume of an n-dimensional ball has a closed form involving π and the gamma function.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical documentation
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Complex.volume_ball` : Volume of open ball in ℂ
- `Complex.volume_closedBall` : Volume of closed ball in ℂ
- `Metric.ball`, `Metric.closedBall` : Ball definitions
- `MeasureTheory.volume` : Lebesgue measure

## Historical Note
The formula A = πr² was known to ancient civilizations, but Archimedes of Syracuse
(c. 287–212 BCE) gave the first rigorous proof using the method of exhaustion—
an ancient precursor to integral calculus. He showed that the area of a circle
equals the area of a right triangle with base equal to the circumference and
height equal to the radius.

This is #9 on Wiedijk's list of 100 theorems.
-/

namespace AreaOfCircle

open MeasureTheory Metric

/-! ## Main Theorem: Area of a Circle

The area (Lebesgue measure) of a 2-dimensional disk with radius r equals πr².

We use the complex plane ℂ as our model for 2D Euclidean space, since ℂ ≅ ℝ²
as real inner product spaces and the formula is most elegant in this form. -/

/-- **Area of a Circle (Wiedijk #9)**

The area of an open disk in the complex plane with radius r is πr².

In formal terms: the Lebesgue measure of the set {z ∈ ℂ : |z - center| < r}
equals r² · π (as an extended non-negative real number).

Since ℂ and ℝ² are isomorphic as real inner product spaces, this proves
the classical result for circles in the Euclidean plane.

Note: For r ≤ 0, the ball is empty and has measure 0. -/
theorem area_of_circle (center : ℂ) (r : ℝ) :
    volume (ball center r) = ENNReal.ofReal r ^ 2 * ↑NNReal.pi :=
  Complex.volume_ball center r

/-- Area of a closed disk in the complex plane.

The closed disk {z : |z - center| ≤ r} has the same area πr² as the open disk,
since the boundary (the circle itself) has measure zero. -/
theorem area_of_closed_disk (center : ℂ) (r : ℝ) :
    volume (closedBall center r) = ENNReal.ofReal r ^ 2 * ↑NNReal.pi :=
  Complex.volume_closedBall center r

/-! ## Properties and Corollaries -/

/-- The unit disk has area π.

This is the special case r = 1, giving Area = π · 1² = π. -/
theorem area_unit_disk :
    volume (ball (0 : ℂ) 1) = ↑NNReal.pi := by
  rw [area_of_circle]
  simp [ENNReal.ofReal_one]

/-- The closed unit disk has area π. -/
theorem area_unit_closed_disk :
    volume (closedBall (0 : ℂ) 1) = ↑NNReal.pi := by
  rw [area_of_closed_disk]
  simp [ENNReal.ofReal_one]

/-- A disk with radius 0 has zero area. -/
theorem area_zero_radius (center : ℂ) :
    volume (ball center 0) = 0 := by
  simp [ball_zero]

/-- A closed disk with radius 0 is a single point and has zero area. -/
theorem area_zero_radius_closed (center : ℂ) :
    volume (closedBall center 0) = 0 := by
  simp [closedBall_zero]

/-- Negative radius gives zero area (the ball is empty). -/
theorem area_negative_radius (center : ℂ) {r : ℝ} (hr : r < 0) :
    volume (ball center r) = 0 := by
  simp [ball_eq_empty.mpr (le_of_lt hr)]

/-! ## Why This Matters

The formula A = πr² is fundamental to mathematics and science:

1. **Geometry**: Foundational for understanding circles, spheres, and curved surfaces.

2. **Calculus**: Often the first integral students compute using polar coordinates:
   A = ∫∫_disk dA = ∫₀²π ∫₀ʳ ρ dρ dθ = π r²

3. **Physics**: Essential for calculating areas in optics, mechanics, thermodynamics.
   For example, the intensity of light through a circular aperture depends on πr².

4. **Probability**: The Gaussian distribution has ∫∫ e^(-x²-y²) dA = π,
   which is computed using this area formula.

5. **Engineering**: Used in calculations for pipes, cables, gears, wheels,
   and countless other circular components.

The appearance of π in this formula is not coincidental—it reflects the deep
connection between circles and the ratio of circumference to diameter. -/

/-! ## The Connection to Circumference

While not proven here, the area formula relates to the circumference C = 2πr through
integration. The disk can be approximated by thin annular rings of width dr:
  dA = (circumference at radius ρ) × dr = 2πρ dρ

Integrating from 0 to r:
  A = ∫₀ʳ 2πρ dρ = π ρ² |₀ʳ = πr²

This is how Archimedes conceptualized the proof, viewing the disk as composed
of infinitely many concentric circular strips. -/

#check area_of_circle
#check area_of_closed_disk
#check area_unit_disk
#check area_negative_radius

end AreaOfCircle
