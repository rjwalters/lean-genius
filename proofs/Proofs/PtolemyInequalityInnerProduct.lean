import Mathlib

/-
# Ptolemy's Inequality in an Arbitrary Real Inner Product Space — OQ-05

## Research Problem: ptolemys-theorem-oq-05

Parent open question (ptolemys-theorem):
  "Can Ptolemy's inequality (AC·BD ≤ AB·CD + AD·BC for arbitrary four points)
   be formalized?"

The gallery already answers this **in the plane**: `PtolemysComplexProof.lean`
proves the inequality for four points of `ℂ` via the algebraic identity
`(z₁-z₃)(z₂-z₄) = (z₁-z₂)(z₃-z₄) + (z₁-z₄)(z₂-z₃)` plus the triangle inequality
for `|·|`.  Mathlib (`Mathlib.Geometry.Euclidean.Sphere.Ptolemy`) proves only the
**equality** case for *cospherical* points.

Neither covers the general metric statement: Ptolemy's inequality holds for any
four points of an arbitrary real inner product space (any dimension), not just the
Euclidean plane.  The complex-identity proof is intrinsically two-dimensional.

This file proves the **general** statement via the *inversion-distance identity*
(the classical proof by inversion), which works in every dimension:

For nonzero `u w` in a real inner product space `V`,
    ‖u‖ · ‖w‖ · ‖ (‖u‖²)⁻¹ • u − (‖w‖²)⁻¹ • w ‖ = ‖u − w‖,           (`inversion_dist`)
i.e. the spherical inversion `x ↦ (‖x‖²)⁻¹ • x` (centred at the origin, radius 1)
scales the distance between `u` and `w` by `1 / (‖u‖ ‖w‖)`.

Applying the triangle inequality to the three inverted points and clearing
denominators yields Ptolemy's inequality with the fourth vertex at the origin:

    ‖x − z‖ · ‖y‖ ≤ ‖x − y‖ · ‖z‖ + ‖y − z‖ · ‖x‖                   (`ptolemy_origin`)

for **all** `x y z : V`.  Translating to a `NormedAddTorsor` gives the four-point
form

    dist a c · dist b d ≤ dist a b · dist c d + dist b c · dist a d  (`ptolemy_dist`)

valid for arbitrary points `a b c d` of any real inner-product affine space.

DISTINCT from the gallery's `PtolemysComplexProof.lean` (ℂ only) and from
Mathlib's cospherical equality: this is the inequality in arbitrary dimension.

Tags: geometry, ptolemy, inner-product-space, inversion, inequality
-/

open RealInnerProductSpace

namespace PtolemyInequalityInnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Inversion distance identity.**  The spherical inversion `x ↦ (‖x‖²)⁻¹ • x`
(centre `0`, radius `1`) sends two nonzero points `u`, `w` to points whose
distance is `‖u − w‖ / (‖u‖ ‖w‖)`.  Stated in denominator-free product form. -/
theorem inversion_dist (u w : V) (hu : u ≠ 0) (hw : w ≠ 0) :
    ‖u‖ * ‖w‖ * ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖ = ‖u - w‖ := by
  have hu0 : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
  have hw0 : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw
  -- Expand the two squared norms via the polarization identity.
  have eab : ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖ ^ 2
      = ‖(‖u‖ ^ 2)⁻¹ • u‖ ^ 2 - 2 * ⟪(‖u‖ ^ 2)⁻¹ • u, (‖w‖ ^ 2)⁻¹ • w⟫
          + ‖(‖w‖ ^ 2)⁻¹ • w‖ ^ 2 :=
    norm_sub_sq_real _ _
  have euw : ‖u - w‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, w⟫ + ‖w‖ ^ 2 := norm_sub_sq_real _ _
  -- The pieces, as plain real expressions.
  have iab : ⟪(‖u‖ ^ 2)⁻¹ • u, (‖w‖ ^ 2)⁻¹ • w⟫
      = (‖u‖ ^ 2)⁻¹ * (‖w‖ ^ 2)⁻¹ * ⟪u, w⟫ := by
    rw [real_inner_smul_left, real_inner_smul_right]; ring
  have na : ‖(‖u‖ ^ 2)⁻¹ • u‖ = (‖u‖ ^ 2)⁻¹ * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have nb : ‖(‖w‖ ^ 2)⁻¹ • w‖ = (‖w‖ ^ 2)⁻¹ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- Squared equality, then take square roots (both sides nonnegative).
  have key : (‖u‖ * ‖w‖ * ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖) ^ 2 = ‖u - w‖ ^ 2 := by
    have expand : (‖u‖ * ‖w‖ * ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖) ^ 2
        = ‖u‖ ^ 2 * ‖w‖ ^ 2 * ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖ ^ 2 := by ring
    rw [expand, eab, iab, na, nb, euw]
    field_simp
    ring
  have hLnn : 0 ≤ ‖u‖ * ‖w‖ * ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖ := by positivity
  calc ‖u‖ * ‖w‖ * ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖
      = Real.sqrt ((‖u‖ * ‖w‖ * ‖(‖u‖ ^ 2)⁻¹ • u - (‖w‖ ^ 2)⁻¹ • w‖) ^ 2) :=
        (Real.sqrt_sq hLnn).symm
    _ = Real.sqrt (‖u - w‖ ^ 2) := by rw [key]
    _ = ‖u - w‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Ptolemy's inequality, fourth vertex at the origin.**  For arbitrary vectors
`x y z` of a real inner product space,
    ‖x − z‖ · ‖y‖ ≤ ‖x − y‖ · ‖z‖ + ‖y − z‖ · ‖x‖.
Any four-point configuration translates to this by moving the fourth point to `0`. -/
theorem ptolemy_origin (x y z : V) :
    ‖x - z‖ * ‖y‖ ≤ ‖x - y‖ * ‖z‖ + ‖y - z‖ * ‖x‖ := by
  -- Degenerate cases: if any vertex coincides with the origin the inequality is
  -- a (possibly trivial) triangle/identity statement.
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp only [zero_sub, norm_neg, norm_zero, mul_zero, add_zero]
    rw [mul_comm]
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    simp only [norm_zero, mul_zero, sub_zero, zero_sub, norm_neg]
    positivity
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    simp only [sub_zero, norm_zero, mul_zero, zero_add]
    rw [mul_comm]
  -- Generic case: apply the triangle inequality to the inverted points.
  set a : V := (‖x‖ ^ 2)⁻¹ • x with ha
  set b : V := (‖y‖ ^ 2)⁻¹ • y with hb
  set c : V := (‖z‖ ^ 2)⁻¹ • z with hc
  -- Inversion distances.
  have I_ac : ‖x‖ * ‖z‖ * ‖a - c‖ = ‖x - z‖ := inversion_dist x z hx hz
  have I_ab : ‖x‖ * ‖y‖ * ‖a - b‖ = ‖x - y‖ := inversion_dist x y hx hy
  have I_bc : ‖y‖ * ‖z‖ * ‖b - c‖ = ‖y - z‖ := inversion_dist y z hy hz
  -- Triangle inequality for the inverted points, scaled by ‖x‖‖y‖‖z‖ > 0.
  have tri : ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := by
    have := dist_triangle a b c
    simpa only [dist_eq_norm] using this
  have scaled : ‖x‖ * ‖y‖ * ‖z‖ * ‖a - c‖
      ≤ ‖x‖ * ‖y‖ * ‖z‖ * (‖a - b‖ + ‖b - c‖) :=
    mul_le_mul_of_nonneg_left tri (by positivity)
  -- Rewrite each scaled distance into a side product.
  have L : ‖x‖ * ‖y‖ * ‖z‖ * ‖a - c‖ = ‖x - z‖ * ‖y‖ := by
    rw [show ‖x‖ * ‖y‖ * ‖z‖ * ‖a - c‖ = (‖x‖ * ‖z‖ * ‖a - c‖) * ‖y‖ by ring, I_ac]
  have R : ‖x‖ * ‖y‖ * ‖z‖ * (‖a - b‖ + ‖b - c‖)
      = ‖x - y‖ * ‖z‖ + ‖y - z‖ * ‖x‖ := by
    rw [mul_add,
      show ‖x‖ * ‖y‖ * ‖z‖ * ‖a - b‖ = (‖x‖ * ‖y‖ * ‖a - b‖) * ‖z‖ by ring, I_ab,
      show ‖x‖ * ‖y‖ * ‖z‖ * ‖b - c‖ = (‖y‖ * ‖z‖ * ‖b - c‖) * ‖x‖ by ring, I_bc]
  rwa [L, R] at scaled

/-- **Ptolemy's inequality for four arbitrary points** of a real inner-product
affine space (a `NormedAddTorsor` over `V`).  For points `a b c d`,
    dist a c · dist b d ≤ dist a b · dist c d + dist b c · dist a d.
Valid in every dimension; the gallery's complex-number proof is two-dimensional. -/
theorem ptolemy_dist {P : Type*} [MetricSpace P] [NormedAddTorsor V P]
    (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d := by
  -- Translate so that `d` is the origin: set x = a -ᵥ d, y = b -ᵥ d, z = c -ᵥ d.
  have h := ptolemy_origin (a -ᵥ d) (b -ᵥ d) (c -ᵥ d)
  -- dist p q = ‖(p -ᵥ d) - (q -ᵥ d)‖, dist p d = ‖p -ᵥ d‖.
  simp only [dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right] at h ⊢
  exact h

/-- Concrete instantiation in `EuclideanSpace ℝ (Fin 3)`: Ptolemy's inequality
holds in three dimensions, where the complex-number proof does not apply. -/
example (a b c d : EuclideanSpace ℝ (Fin 3)) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d :=
  ptolemy_dist a b c d

end PtolemyInequalityInnerProduct
