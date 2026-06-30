/-
# Heron's Formula OQ-05: The Cayley–Menger Determinant

Generalize Heron's formula to simplex volume from squared edge lengths via the
Cayley–Menger determinant.

For points `P₀, …, Pₙ` in Euclidean space, the Cayley–Menger determinant of the
`(n+2) × (n+2)` matrix

      ⎡ 0  1   1   …  1  ⎤
      ⎢ 1  0  d₀₁ … d₀ₙ ⎥
      ⎢ 1 d₀₁  0  … d₁ₙ ⎥        (dᵢⱼ = ‖Pᵢ - Pⱼ‖²)
      ⎢ ⋮               ⎥
      ⎣ 1 d₀ₙ d₁ₙ …  0  ⎦

equals `(-1)^(n+1) · 2^n · (n!)² · V²`, where `V` is the `n`-dimensional content
of the simplex.

This file formalizes the two classical cases as explicit polynomial identities in
the squared edge lengths:

* **n = 2 (Heron):** `cmDet3 = -4 · (2·Area)²`, i.e. `16·Area² = -cmDet3`.
  Expanding the squared distances recovers the symmetric form of Heron's formula.
* **n = 3 (tetrahedron):** `cmDet4 = 8 · (6·V)²`, i.e. `288·V² = cmDet4`.

The polynomials `cmDet3` / `cmDet4` are the (expanded) Cayley–Menger determinants
of the 4×4 / 5×5 matrices above; the constant terms `-4` / `8` are exactly
`(-1)^(n+1) · 2^n · (n!)² / (n!)²`-normalised against the `(n!·V)`-form of the
content used here (`2·Area` and `6·V` are the unsigned `n!·V` scalars).

## Status: Verified (0 axioms, 0 sorries)
-/

import Mathlib.Tactic

namespace CayleyMengerHeron

/-! ## Two-dimensional case (Heron's formula) -/

abbrev Point2 := ℝ × ℝ

/-- Squared Euclidean distance between two points of the plane. -/
def sqDist2 (p q : Point2) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Twice the signed area of triangle `P₀P₁P₂` (the `2!·Area` scalar). -/
def area2 (P₀ P₁ P₂ : Point2) : ℝ :=
  (P₁.1 - P₀.1) * (P₂.2 - P₀.2) - (P₂.1 - P₀.1) * (P₁.2 - P₀.2)

/-- The Cayley–Menger determinant of a triangle, as a polynomial in the three
squared edge lengths `d₀₁, d₀₂, d₁₂`. This is `det` of

      ⎡ 0  1   1   1  ⎤
      ⎢ 1  0  d₀₁ d₀₂ ⎥
      ⎢ 1 d₀₁  0  d₁₂ ⎥
      ⎣ 1 d₀₂ d₁₂  0  ⎦ -/
def cmDet3 (d01 d02 d12 : ℝ) : ℝ :=
  d01 ^ 2 - 2 * d01 * d02 - 2 * d01 * d12 + d02 ^ 2 - 2 * d02 * d12 + d12 ^ 2

/-- **Cayley–Menger identity (triangle).** The Cayley–Menger determinant of three
planar points equals `-4` times the square of twice their signed area. -/
theorem cmDet3_eq (P₀ P₁ P₂ : Point2) :
    cmDet3 (sqDist2 P₀ P₁) (sqDist2 P₀ P₂) (sqDist2 P₁ P₂)
      = -4 * (area2 P₀ P₁ P₂) ^ 2 := by
  simp only [cmDet3, sqDist2, area2]; ring

/-- **Heron's formula (Cayley–Menger form).** With `Area = |area2| / 2` the squared
area of a triangle is recovered from its squared edge lengths:
`16·Area² = -cmDet3`. -/
theorem heron_sixteen_area_sq (P₀ P₁ P₂ : Point2) :
    16 * (|area2 P₀ P₁ P₂| / 2) ^ 2
      = -cmDet3 (sqDist2 P₀ P₁) (sqDist2 P₀ P₂) (sqDist2 P₁ P₂) := by
  rw [cmDet3_eq, div_pow, sq_abs]; ring

/-! ## Three-dimensional case (tetrahedron volume) -/

abbrev Point3 := ℝ × ℝ × ℝ

/-- Squared Euclidean distance between two points of space. -/
def sqDist3 (p q : Point3) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2

/-- Six times the signed volume of tetrahedron `P₀P₁P₂P₃` (the `3!·V` scalar): the
scalar triple product `(P₁-P₀) · ((P₂-P₀) × (P₃-P₀))`. -/
def vol6 (P₀ P₁ P₂ P₃ : Point3) : ℝ :=
  (P₁.1 - P₀.1) *
      ((P₂.2.1 - P₀.2.1) * (P₃.2.2 - P₀.2.2) - (P₂.2.2 - P₀.2.2) * (P₃.2.1 - P₀.2.1))
  - (P₁.2.1 - P₀.2.1) *
      ((P₂.1 - P₀.1) * (P₃.2.2 - P₀.2.2) - (P₂.2.2 - P₀.2.2) * (P₃.1 - P₀.1))
  + (P₁.2.2 - P₀.2.2) *
      ((P₂.1 - P₀.1) * (P₃.2.1 - P₀.2.1) - (P₂.2.1 - P₀.2.1) * (P₃.1 - P₀.1))

/-- The Cayley–Menger determinant of a tetrahedron, as a polynomial in the six
squared edge lengths. This is `det` of the 5×5 matrix

      ⎡ 0  1   1   1   1  ⎤
      ⎢ 1  0  d₀₁ d₀₂ d₀₃ ⎥
      ⎢ 1 d₀₁  0  d₁₂ d₁₃ ⎥
      ⎢ 1 d₀₂ d₁₂  0  d₂₃ ⎥
      ⎣ 1 d₀₃ d₁₃ d₂₃  0  ⎦ -/
def cmDet4 (d01 d02 d03 d12 d13 d23 : ℝ) : ℝ :=
  -2 * d01 ^ 2 * d23 - 2 * d01 * d02 * d12 + 2 * d01 * d02 * d13
  + 2 * d01 * d02 * d23 + 2 * d01 * d03 * d12 - 2 * d01 * d03 * d13
  + 2 * d01 * d03 * d23 + 2 * d01 * d12 * d23 + 2 * d01 * d13 * d23
  - 2 * d01 * d23 ^ 2 - 2 * d02 ^ 2 * d13 + 2 * d02 * d03 * d12
  + 2 * d02 * d03 * d13 - 2 * d02 * d03 * d23 + 2 * d02 * d12 * d13
  - 2 * d02 * d13 ^ 2 + 2 * d02 * d13 * d23 - 2 * d03 ^ 2 * d12
  - 2 * d03 * d12 ^ 2 + 2 * d03 * d12 * d13 + 2 * d03 * d12 * d23
  - 2 * d12 * d13 * d23

/-- **Cayley–Menger identity (tetrahedron).** The Cayley–Menger determinant of
four points in space equals `8` times the square of six times their signed
volume. -/
theorem cmDet4_eq (P₀ P₁ P₂ P₃ : Point3) :
    cmDet4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
           (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃)
      = 8 * (vol6 P₀ P₁ P₂ P₃) ^ 2 := by
  simp only [cmDet4, sqDist3, vol6]; ring

/-- **Simplex volume from squared edges (tetrahedron).** With `V = |vol6| / 6`
the squared volume of a tetrahedron is recovered from its six squared edge
lengths: `288·V² = cmDet4`. -/
theorem cayley_menger_tetrahedron (P₀ P₁ P₂ P₃ : Point3) :
    288 * (|vol6 P₀ P₁ P₂ P₃| / 6) ^ 2
      = cmDet4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
               (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃) := by
  rw [cmDet4_eq, div_pow, sq_abs]; ring

/-- The tetrahedral Cayley–Menger determinant is nonnegative: the realizability
form `288·V² = cmDet4 ≥ 0` holds for any four points. -/
theorem cmDet4_nonneg (P₀ P₁ P₂ P₃ : Point3) :
    0 ≤ cmDet4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
               (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃) := by
  rw [cmDet4_eq]; positivity

/-- **Degeneracy criterion.** Four points are coplanar (zero volume) iff their
Cayley–Menger determinant vanishes. -/
theorem cmDet4_eq_zero_iff_coplanar (P₀ P₁ P₂ P₃ : Point3) :
    cmDet4 (sqDist3 P₀ P₁) (sqDist3 P₀ P₂) (sqDist3 P₀ P₃)
           (sqDist3 P₁ P₂) (sqDist3 P₁ P₃) (sqDist3 P₂ P₃) = 0
      ↔ vol6 P₀ P₁ P₂ P₃ = 0 := by
  rw [cmDet4_eq]
  constructor
  · intro h
    have : (vol6 P₀ P₁ P₂ P₃) ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  · intro h; rw [h]; ring

end CayleyMengerHeron
