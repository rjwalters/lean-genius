import Mathlib

/-
# Viviani's Theorem

## Statement

For any point `P` inside an equilateral triangle, the sum of the perpendicular
distances from `P` to the three sides equals the altitude of the triangle.

## Formalization

We work in coordinates. Take the unit-side equilateral triangle with vertices

  `A = (0, 0)`,  `B = (1, 0)`,  `C = (1/2, √3/2)`.

Its three sides lie on the lines

  `AB :  Y = 0`              i.e.  `0·X + 1·Y + 0 = 0`
  `AC :  √3·X − Y = 0`        i.e.  `√3·X + (−1)·Y + 0 = 0`
  `BC :  √3·X + Y − √3 = 0`   i.e.  `√3·X + 1·Y + (−√3) = 0`

The perpendicular distance from a point `(x, y)` to the line `a·X + b·Y + c = 0`
is the standard formula `|a·x + b·y + c| / √(a² + b²)`, captured by `distToLine`.

The interior of the triangle is the intersection of the three half-planes
`y ≥ 0`, `√3·x − y ≥ 0`, `√3·x + y − √3 ≤ 0`. On the interior the absolute
values resolve with fixed signs, and the three distances become

  `d_AB = y`,
  `d_AC = (√3·x − y)/2`,
  `d_BC = (√3 − √3·x − y)/2`,

whose sum is `√3/2`, the altitude — independent of the point `(x, y)`.

**No axioms, no sorries.** Self-contained (Mathlib only).

## Main results

* `distToLine`           : perpendicular distance from a point to a line.
* `viviani`              : the sum of the three distances equals `√3/2`.
* `altitude_eq`          : the altitude (apex-to-base distance) is `√3/2`,
                           justifying the right-hand side.
* `interior_nonempty`    : the centroid satisfies the interior constraints,
                           so the hypothesis set is non-vacuous.
-/

namespace VivianiTheorem

open Real

/-- Perpendicular distance from the point `(x, y)` to the line
`a · X + b · Y + c = 0`. -/
noncomputable def distToLine (a b c x y : ℝ) : ℝ :=
  |a * x + b * y + c| / Real.sqrt (a ^ 2 + b ^ 2)

/-- `(√3)² = 3`, the only irrational fact used below. -/
private lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- Distance to the base `AB : Y = 0` of a point with `y ≥ 0` is `y`. -/
lemma dist_AB {x y : ℝ} (hy : 0 ≤ y) :
    distToLine 0 1 0 x y = y := by
  unfold distToLine
  rw [show ((0 : ℝ) ^ 2 + (1 : ℝ) ^ 2) = 1 by norm_num, Real.sqrt_one, div_one,
    show (0 : ℝ) * x + 1 * y + 0 = y by ring]
  exact abs_of_nonneg hy

/-- Distance to the side `AC : √3·X − Y = 0` of an interior point is
`(√3·x − y)/2`. -/
lemma dist_AC {x y : ℝ} (hAC : 0 ≤ Real.sqrt 3 * x - y) :
    distToLine (Real.sqrt 3) (-1) 0 x y = (Real.sqrt 3 * x - y) / 2 := by
  unfold distToLine
  rw [show (Real.sqrt 3 ^ 2 + (-1 : ℝ) ^ 2) = 4 by rw [sqrt3_sq]; norm_num,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
    show Real.sqrt 3 * x + (-1) * y + 0 = Real.sqrt 3 * x - y by ring,
    abs_of_nonneg hAC]

/-- Distance to the side `BC : √3·X + Y − √3 = 0` of an interior point is
`(√3 − √3·x − y)/2`. -/
lemma dist_BC {x y : ℝ} (hBC : Real.sqrt 3 * x + y - Real.sqrt 3 ≤ 0) :
    distToLine (Real.sqrt 3) 1 (-Real.sqrt 3) x y
      = (Real.sqrt 3 - Real.sqrt 3 * x - y) / 2 := by
  unfold distToLine
  rw [show (Real.sqrt 3 ^ 2 + (1 : ℝ) ^ 2) = 4 by rw [sqrt3_sq]; norm_num,
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
    show Real.sqrt 3 * x + 1 * y + (-Real.sqrt 3)
      = Real.sqrt 3 * x + y - Real.sqrt 3 by ring,
    abs_of_nonpos hBC]
  ring

/-- **Viviani's theorem.** For any point `(x, y)` in the (closed) unit-side
equilateral triangle `A = (0,0)`, `B = (1,0)`, `C = (1/2, √3/2)`, the sum of the
perpendicular distances to the three sides equals the altitude `√3/2`,
independently of the point. -/
theorem viviani {x y : ℝ}
    (hAB : 0 ≤ y)
    (hAC : 0 ≤ Real.sqrt 3 * x - y)
    (hBC : Real.sqrt 3 * x + y - Real.sqrt 3 ≤ 0) :
    distToLine 0 1 0 x y
      + distToLine (Real.sqrt 3) (-1) 0 x y
      + distToLine (Real.sqrt 3) 1 (-Real.sqrt 3) x y
      = Real.sqrt 3 / 2 := by
  rw [dist_AB hAB, dist_AC hAC, dist_BC hBC]
  ring

/-- The altitude of the unit-side equilateral triangle is `√3/2`: the
perpendicular distance from the apex `C = (1/2, √3/2)` to the base
`AB : Y = 0` equals `√3/2`. This justifies the right-hand side of `viviani`. -/
theorem altitude_eq :
    distToLine 0 1 0 (1 / 2) (Real.sqrt 3 / 2) = Real.sqrt 3 / 2 := by
  have h : (0 : ℝ) ≤ Real.sqrt 3 / 2 := by positivity
  exact dist_AB h

/-- The centroid `(1/2, √3/6)` of the triangle satisfies the three interior
constraints, so the hypotheses of `viviani` are non-vacuous. -/
theorem interior_nonempty :
    (0 ≤ (Real.sqrt 3) / 6)
      ∧ (0 ≤ Real.sqrt 3 * (1 / 2) - Real.sqrt 3 / 6)
      ∧ (Real.sqrt 3 * (1 / 2) + Real.sqrt 3 / 6 - Real.sqrt 3 ≤ 0) := by
  have h3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  refine ⟨by positivity, by nlinarith, by nlinarith⟩

end VivianiTheorem
