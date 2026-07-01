import Mathlib

/-!
# Napoleon's area theorem (outer + inner = original), signed form — napoleons-theorem-oq-04

The parent entry `napoleons-theorem` proves the outer Napoleon triangle is equilateral.
This child proves the classical *area* companion: the difference between the areas of the
outer and inner Napoleon triangles equals the area of the original triangle.

## Signs and the centroid formula (two corrections to the seeker sketch)

The problem's Lean sketch contained two inaccuracies that make the *literal* statement
false; this file states and proves the correct identity.

1. **Centroid, not apex.** The Napoleon triangle is built from the **centroids** of the
   equilateral triangles on the sides, not their apices. The centroid of the equilateral
   triangle on side `pq` sits at perpendicular offset `|q-p|·√3/6` from the midpoint
   (the apex is at `√3/2`); the sketch's `√3/2` is the apex distance and does not satisfy
   the area identity. We use the centroid, coefficient `√3/6`.

2. **Orientation.** With the *signed* area `triArea a b c = ½ Im((b-a) · conj (c-a))`
   (the sketch's own code convention) and the **same** cyclic vertex ordering for both
   Napoleon triangles, the inner triangle is oppositely oriented, so its signed area is the
   negative of its unsigned area. The clean signed identity is therefore an **addition**
   `triArea(outer) + triArea(inner) = triArea(original)` (`napoleon_area_signed`), which is
   exactly the classical *unsigned* statement `|outer| − |inner| = |original|`. Listing the
   inner triangle's vertices in the opposite (natural) order recovers the literal
   subtraction form `triArea(outer) − triArea(inner) = triArea(original)`
   (`napoleon_area_difference`).

The core is a finite complex-algebra cancellation: expand the three signed areas into real
coordinates, substitute the centroid formulas, and observe that the `√3`-linear terms cancel
between the outer and inner triangles while `√3² = 3` closes the rest. Verified 0-axiom.
-/

open Complex ComplexConjugate

namespace NapoleonArea

/-- Signed area of the triangle `a b c`, `½ Im((b-a) · conj (c-a))` (sketch code convention;
counterclockwise triples get positive area up to this orientation choice). -/
noncomputable def triArea (a b c : ℂ) : ℝ := (((b - a) * conj (c - a)).im) / 2

/-- Real-coordinate expansion of the signed area (a cross product of the two edge vectors). -/
theorem triArea_eq (a b c : ℂ) :
    triArea a b c =
      ((b.im - a.im) * (c.re - a.re) - (b.re - a.re) * (c.im - a.im)) / 2 := by
  simp only [triArea, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Centroid of the equilateral triangle erected on side `pq`, on the `r`-side
(`r = 1` outward, `r = -1` inward). This is the geometric centroid
`(p+q)/2 + (q-p)·(I · r · √3/6)`; note the coefficient is `√3/6` (centroid), *not* `√3/2`
(apex). -/
noncomputable def napCentroid (p q : ℂ) (r : ℝ) : ℂ :=
  (p + q) * Complex.ofReal (1 / 2)
    + (q - p) * (Complex.I * Complex.ofReal (r * Real.sqrt 3 / 6))

theorem napCentroid_re (p q : ℂ) (r : ℝ) :
    (napCentroid p q r).re =
      (p.re + q.re) / 2 - r * Real.sqrt 3 / 6 * (q.im - p.im) := by
  simp only [napCentroid, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

theorem napCentroid_im (p q : ℂ) (r : ℝ) :
    (napCentroid p q r).im =
      (p.im + q.im) / 2 + r * Real.sqrt 3 / 6 * (q.re - p.re) := by
  simp only [napCentroid, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- **Napoleon's area theorem (signed form).** For any triangle `z₁ z₂ z₃`, the signed area
of the outward Napoleon triangle plus the signed area of the inward Napoleon triangle
(both with the same cyclic vertex ordering) equals the signed area of `z₁ z₂ z₃`.

Because the inward triangle is oppositely oriented, its signed area is the negative of its
unsigned area, so this is the classical `|outer| − |inner| = |original|`.

Proof: expand via `triArea_eq` and the centroid formulas; the `√3`-linear contributions of
the two Napoleon triangles cancel, and the residual is closed by `√3² = 3`. -/
theorem napoleon_area_signed (z₁ z₂ z₃ : ℂ) :
    triArea (napCentroid z₂ z₃ 1) (napCentroid z₃ z₁ 1) (napCentroid z₁ z₂ 1)
      + triArea (napCentroid z₂ z₃ (-1)) (napCentroid z₃ z₁ (-1)) (napCentroid z₁ z₂ (-1))
      = triArea z₁ z₂ z₃ := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  simp only [triArea_eq, napCentroid_re, napCentroid_im]
  linear_combination
    (-z₁.re * z₂.im + z₁.re * z₃.im + z₂.re * z₁.im - z₂.re * z₃.im
      - z₃.re * z₁.im + z₃.re * z₂.im) / 12 * hs

/-- **Napoleon's area theorem (difference form).** Listing the inner Napoleon triangle's
vertices in its natural (opposite) orientation turns the signed identity into the literal
classical statement: the outer Napoleon area *minus* the inner Napoleon area equals the
original area. -/
theorem napoleon_area_difference (z₁ z₂ z₃ : ℂ) :
    triArea (napCentroid z₂ z₃ 1) (napCentroid z₃ z₁ 1) (napCentroid z₁ z₂ 1)
      - triArea (napCentroid z₂ z₃ (-1)) (napCentroid z₁ z₂ (-1)) (napCentroid z₃ z₁ (-1))
      = triArea z₁ z₂ z₃ := by
  have h := napoleon_area_signed z₁ z₂ z₃
  have e : triArea (napCentroid z₂ z₃ (-1)) (napCentroid z₁ z₂ (-1)) (napCentroid z₃ z₁ (-1))
      = -triArea (napCentroid z₂ z₃ (-1)) (napCentroid z₃ z₁ (-1)) (napCentroid z₁ z₂ (-1)) := by
    simp only [triArea_eq]; ring
  rw [e]; linarith

/-! ### Worked examples -/

/-- A degenerate triangle with two coincident vertices has zero area. -/
example (a b : ℂ) : triArea a b b = 0 := by rw [triArea_eq]; ring

/-- Signed area of the unit right triangle `0, 1, i` is `-1/2` in this orientation
convention. -/
example : triArea 0 1 Complex.I = -1 / 2 := by
  simp only [triArea_eq, Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  norm_num

end NapoleonArea
