import Mathlib
import Proofs.CarnotTheoremOQ01OQ03
import Proofs.CarnotTheoremOQ01OQ03OQ01

/-
# Carnot's Theorem — the law-of-sines bridge: a sharp *geometric* perimeter bound

The companion files develop the angle-level sine sum for a triangle:

* `CarnotTheoremOQ01OQ03.lean` proves the sharp bound
  `sin A + sin B + sin C ≤ 3√3 / 2`   (for `A + B + C = π`, `A, B, C ∈ [0, π]`);
* `CarnotTheoremOQ01OQ03OQ01.lean` upgrades it to a uniqueness statement:
  equality holds **iff** `A = B = C = π/3`.

Both are statements about *reals* `A, B, C` summing to `π`. The parent entry left a
second open question:

> *Formalise the law-of-sines bridge to express the bound as an explicit perimeter
> inequality over `EuclideanSpace ℝ (Fin 2)`.*

This file does exactly that. For an honest geometric triangle — a value of Mathlib's
`Affine.Triangle ℝ P` in any real inner-product space `P` (e.g. `EuclideanSpace ℝ (Fin 2)`,
the Euclidean plane) — with circumradius `R = t.circumradius`, the **extended law of sines**
(`Affine.Triangle.dist_div_sin_angle_eq_two_mul_circumradius`) gives each side length as

  `(side opposite vertex i) = 2R · sin(interior angle at i)`.

Summing the three sides,

  `perimeter t = 2R · (sin A + sin B + sin C)`,

so the angle-level bound becomes a **geometric perimeter inequality**:

  `perimeter t ≤ 3√3 · R`,

with equality **iff** the triangle is equiangular (`A = B = C = π/3`), i.e. equilateral.
This is the classical fact that *among all triangles inscribed in a fixed circle the
equilateral one has the greatest perimeter*, now machine-verified end to end.

The three ingredients are:

* the **extended law of sines** from Mathlib, plus `angle_pos_of_not_collinear` /
  `angle_lt_pi_of_not_collinear` to clear the `sin ≠ 0` denominator (the triangle's
  affine independence makes each interior angle lie strictly in `(0, π)`);
* the Euclidean **angle sum** `angle_add_angle_add_angle_eq_pi` to feed the hypothesis
  `A + B + C = π`;
* the companion **angle-level results** `sin_sum_le` and `sin_sum_eq_iff_equilateral`,
  reused verbatim — the bridge does no new trigonometry, only geometry.

**No axioms, no sorries.**
-/

open Real EuclideanGeometry

namespace CarnotTheoremOQ01OQ03OQ02

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- **One side of a triangle as `2R · sin(opposite angle)`.** For a triangle
`t : Triangle ℝ P` and three *distinct* vertex indices `i₁, i₂, i₃`, the side joining
`i₁` and `i₃` has length `2 · circumradius · sin(∠ at i₂)`.

This is the extended law of sines `dist_div_sin_angle_eq_two_mul_circumradius` with the
denominator cleared: affine independence of the triangle forces the interior angle at
`i₂` into the open interval `(0, π)` (`angle_pos_of_not_collinear` /
`angle_lt_pi_of_not_collinear`), so its sine is nonzero and the division is legitimate. -/
private lemma side_eq_two_mul_circumradius_mul_sin (t : Affine.Triangle ℝ P)
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.points i₁) (t.points i₃)
      = 2 * t.circumradius
          * Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) := by
  have hnc : ¬ Collinear ℝ ({t.points i₁, t.points i₂, t.points i₃} : Set P) :=
    (affineIndependent_iff_not_collinear_of_ne h₁₂ h₁₃ h₂₃).mp t.independent
  have hsin : Real.sin (∠ (t.points i₁) (t.points i₂) (t.points i₃)) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (angle_pos_of_not_collinear hnc) (angle_lt_pi_of_not_collinear hnc))
  have hlos := t.dist_div_sin_angle_eq_two_mul_circumradius h₁₂ h₁₃ h₂₃
  rw [div_eq_iff hsin] at hlos
  linear_combination hlos

/-- **The interior angles of a triangle sum to `π`.** Convenience restatement of
`angle_add_angle_add_angle_eq_pi`, in the vertex ordering used below: the angle at
vertex `0` is `∠ p₁ p₀ p₂`, at vertex `1` is `∠ p₂ p₁ p₀`, at vertex `2` is `∠ p₀ p₂ p₁`. -/
private lemma angle_sum_eq_pi (t : Affine.Triangle ℝ P) :
    ∠ (t.points 1) (t.points 0) (t.points 2)
      + ∠ (t.points 2) (t.points 1) (t.points 0)
      + ∠ (t.points 0) (t.points 2) (t.points 1) = π := by
  have h := angle_add_angle_add_angle_eq_pi (p₁ := t.points 1) (p₂ := t.points 0)
    (t.points 2) (t.independent.injective.ne (by decide))
  linarith [h]

/-- **Sharp geometric perimeter bound (the law-of-sines bridge).** For any triangle
`t : Triangle ℝ P` in a real inner-product space (e.g. the Euclidean plane
`EuclideanSpace ℝ (Fin 2)`), the perimeter is at most `3√3` times the circumradius:

  `dist p₀ p₁ + dist p₁ p₂ + dist p₂ p₀ ≤ 3√3 · t.circumradius`.

Each side equals `2R · sin(opposite angle)` (extended law of sines), so the perimeter is
`2R · (sin A + sin B + sin C)`; the angle sum is `π`, so the companion bound
`sin A + sin B + sin C ≤ 3√3/2` gives the claim (`R ≥ 0`). Geometrically: among all
triangles inscribed in a fixed circle the perimeter never exceeds that of the
equilateral one. -/
theorem perimeter_le (t : Affine.Triangle ℝ P) :
    dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2)
        + dist (t.points 2) (t.points 0)
      ≤ 3 * Real.sqrt 3 * t.circumradius := by
  have sA := side_eq_two_mul_circumradius_mul_sin t
    (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
  have sB := side_eq_two_mul_circumradius_mul_sin t
    (i₁ := 2) (i₂ := 1) (i₃ := 0) (by decide) (by decide) (by decide)
  have sC := side_eq_two_mul_circumradius_mul_sin t
    (i₁ := 0) (i₂ := 2) (i₃ := 1) (by decide) (by decide) (by decide)
  have hbound := CarnotTheoremOQ01OQ03.sin_sum_le _ _ _
    (angle_nonneg _ _ _) (angle_nonneg _ _ _) (angle_nonneg _ _ _) (angle_sum_eq_pi t)
  have hR : 0 ≤ t.circumradius := t.circumradius_nonneg
  have hslack : t.circumradius
      * (Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))
          + Real.sin (∠ (t.points 2) (t.points 1) (t.points 0))
          + Real.sin (∠ (t.points 0) (t.points 2) (t.points 1)))
        ≤ t.circumradius * (3 * Real.sqrt 3 / 2) :=
    mul_le_mul_of_nonneg_left hbound hR
  rw [sC, sA, sB]
  nlinarith [hslack, hR, hbound]

/-- **Equality holds iff the triangle is equilateral (equiangular).** The perimeter bound
`perimeter t ≤ 3√3 · R` is attained *exactly* when all three interior angles equal `π/3`:

  `dist p₀ p₁ + dist p₁ p₂ + dist p₂ p₀ = 3√3 · t.circumradius`
    `↔ ∠ at 0 = π/3 ∧ ∠ at 1 = π/3 ∧ ∠ at 2 = π/3`.

The circumradius of a genuine triangle is positive (`circumradius_pos`), so cancelling
`2R` turns the perimeter equation into `sin A + sin B + sin C = 3√3/2`, which the
companion uniqueness result `sin_sum_eq_iff_equilateral` pins to the equiangular triangle.
This is the sharp form of Carnot's perimeter bridge: the equilateral triangle is the
unique maximal-perimeter triangle inscribed in a fixed circle. -/
theorem perimeter_eq_iff_equilateral (t : Affine.Triangle ℝ P) :
    dist (t.points 0) (t.points 1) + dist (t.points 1) (t.points 2)
        + dist (t.points 2) (t.points 0) = 3 * Real.sqrt 3 * t.circumradius
      ↔ ∠ (t.points 1) (t.points 0) (t.points 2) = π / 3
        ∧ ∠ (t.points 2) (t.points 1) (t.points 0) = π / 3
        ∧ ∠ (t.points 0) (t.points 2) (t.points 1) = π / 3 := by
  have sA := side_eq_two_mul_circumradius_mul_sin t
    (i₁ := 1) (i₂ := 0) (i₃ := 2) (by decide) (by decide) (by decide)
  have sB := side_eq_two_mul_circumradius_mul_sin t
    (i₁ := 2) (i₂ := 1) (i₃ := 0) (by decide) (by decide) (by decide)
  have sC := side_eq_two_mul_circumradius_mul_sin t
    (i₁ := 0) (i₂ := 2) (i₃ := 1) (by decide) (by decide) (by decide)
  have hRpos : 0 < t.circumradius := t.circumradius_pos
  have h2R : (2 * t.circumradius) ≠ 0 := mul_ne_zero two_ne_zero (ne_of_gt hRpos)
  have hiff := CarnotTheoremOQ01OQ03OQ01.sin_sum_eq_iff_equilateral
    (∠ (t.points 1) (t.points 0) (t.points 2))
    (∠ (t.points 2) (t.points 1) (t.points 0))
    (∠ (t.points 0) (t.points 2) (t.points 1))
    (angle_nonneg _ _ _) (angle_nonneg _ _ _) (angle_nonneg _ _ _) (angle_sum_eq_pi t)
  rw [sC, sA, sB,
    show (2 * t.circumradius * Real.sin (∠ (t.points 0) (t.points 2) (t.points 1))
          + 2 * t.circumradius * Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))
          + 2 * t.circumradius * Real.sin (∠ (t.points 2) (t.points 1) (t.points 0)))
        = 2 * t.circumradius
            * (Real.sin (∠ (t.points 1) (t.points 0) (t.points 2))
                + Real.sin (∠ (t.points 2) (t.points 1) (t.points 0))
                + Real.sin (∠ (t.points 0) (t.points 2) (t.points 1))) from by ring,
    show (3 * Real.sqrt 3 * t.circumradius)
        = 2 * t.circumradius * (3 * Real.sqrt 3 / 2) from by ring,
    mul_right_inj' h2R]
  exact hiff

end CarnotTheoremOQ01OQ03OQ02
