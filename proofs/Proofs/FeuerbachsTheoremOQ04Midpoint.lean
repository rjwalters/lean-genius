/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): spherical side-midpoints

This companion file to `Proofs.FeuerbachsTheoremOQ04` supplies the **spherical midpoint**
of two model points and, feeding it into the merged circumcircle primitive, the existence of
the **spherical nine-point circle** of a spherical triangle.

## Why this matters for Feuerbach

The spherical **nine-point circle** of a spherical triangle is the circumcircle of its
*medial triangle* — the triangle whose vertices are the three side-midpoints.  The merged
`sphericalCircumcircle_exists` (companion file `FeuerbachsTheoremOQ04Circumcircle.lean`)
already produces a common circle through any three model points; the one missing ingredient
was a genuine **midpoint** of a spherical side.  This file supplies exactly that primitive
and closes the long-standing frontier item "side-midpoints (`sMidpoint`), in-flight".

## The construction

For two model points `A, B` on the sphere the natural midpoint of the (minor) great-circle
arc `AB` is the normalised sum `sMidpoint A B = ‖A + B‖⁻¹ • (A + B)`.  Being a positive
combination of `A` and `B`, it lies on the great circle through them and — crucially — is
spherically equidistant from both: `⟪A, A+B⟫ = 1 + ⟪A,B⟫ = ⟪B, A+B⟫`, so `scos A M = scos B M`
and hence `sdist A M = sdist B M`.  Equivalently `M` is orthogonal to the pole `A − B`, i.e.
lies on the spherical perpendicular bisector of `AB` characterised in
`inner_sub_eq_zero_iff_scos_eq`.  The construction is well-defined precisely when `A` and `B`
are not antipodal (`A + B ≠ 0`) — a genuine spherical nondegeneracy condition, since two
antipodal points bound infinitely many geodesics and have no unique midpoint.

Everything is built on the *merged* metric/circle API of `Proofs.FeuerbachsTheoremOQ04`
(`OnSphere`, `scos`, `sdist`, `sCircle`) and the merged `sphericalCircumcircle_exists`; this
file adds no axioms and no sorries.

## What this file proves (0 axioms, 0 sorries)

* `sMidpoint` — the spherical midpoint `‖A + B‖⁻¹ • (A + B)`.
* `sMidpoint_comm` — symmetry `sMidpoint A B = sMidpoint B A`.
* `onSphere_sMidpoint` — for non-antipodal `A, B` (`A + B ≠ 0`) the midpoint is a model point.
* `inner_sMidpoint_sub` — the midpoint lies on the perpendicular bisector: `⟪M, A − B⟫ = 0`.
* `scos_sMidpoint_eq` / `sdist_sMidpoint_eq` — the midpoint is spherically equidistant from the
  two endpoints.
* `sphericalNinePointCircle_exists` — **existence of the spherical nine-point circle**: the
  three side-midpoints of a spherical triangle lie on a common spherical circle.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04
import Proofs.FeuerbachsTheoremOQ04Circumcircle

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The spherical midpoint** of two model points `A, B`: the normalised sum
`‖A + B‖⁻¹ • (A + B)`.  When `A` and `B` are not antipodal this is the midpoint of the minor
great-circle arc joining them — the unique point of that arc equidistant from both endpoints. -/
noncomputable def sMidpoint (A B : E) : E := (‖A + B‖)⁻¹ • (A + B)

/-- The spherical midpoint is symmetric in its two arguments. -/
theorem sMidpoint_comm (A B : E) : sMidpoint A B = sMidpoint B A := by
  unfold sMidpoint; rw [add_comm A B]

/-- **The midpoint of a non-degenerate spherical side is a model point.**  For non-antipodal
`A, B` (`A + B ≠ 0`) the normalised sum has unit norm.  The hypothesis is genuinely needed:
antipodal points sum to `0` and have no well-defined midpoint. -/
theorem onSphere_sMidpoint {A B : E} (h : A + B ≠ 0) : OnSphere (sMidpoint A B) := by
  unfold OnSphere sMidpoint
  rw [norm_smul, norm_inv, norm_norm]
  exact inv_mul_cancel₀ (by rwa [ne_eq, norm_eq_zero])

/-- **The midpoint lies on the spherical perpendicular bisector of `AB`.**  It is orthogonal
to the pole `A − B`, since `⟪A + B, A − B⟫ = ‖A‖² − ‖B‖² = 0` for two model points.  By
`inner_sub_eq_zero_iff_scos_eq` this is the equidistance property in disguise. -/
theorem inner_sMidpoint_sub (A B : E) (hA : OnSphere A) (hB : OnSphere B) :
    (⟪sMidpoint A B, A - B⟫ : ℝ) = 0 := by
  unfold OnSphere at hA hB
  unfold sMidpoint
  rw [real_inner_smul_left, inner_sub_right, inner_add_left, inner_add_left,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hA, hB, real_inner_comm B A]
  ring

/-- **The spherical midpoint is equidistant (equal spherical cosine) from the two endpoints.**
`scos A M = ‖A+B‖⁻¹ (1 + ⟪A,B⟫) = scos B M`, so `A` and `B` are on a common spherical circle
about `M`. -/
theorem scos_sMidpoint_eq (A B : E) (hA : OnSphere A) (hB : OnSphere B) :
    scos A (sMidpoint A B) = scos B (sMidpoint A B) := by
  unfold OnSphere at hA hB
  unfold scos sMidpoint
  rw [real_inner_smul_right, real_inner_smul_right, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hA, hB, real_inner_comm B A]
  ring

/-- **The spherical midpoint is spherically equidistant from the two endpoints.**
`sdist A M = sdist B M`, the defining "midpoint" property, obtained from `scos_sMidpoint_eq`
via `sdist = arccos ∘ scos`. -/
theorem sdist_sMidpoint_eq (A B : E) (hA : OnSphere A) (hB : OnSphere B) :
    sdist A (sMidpoint A B) = sdist B (sMidpoint A B) := by
  have h := scos_sMidpoint_eq A B hA hB
  unfold scos at h
  unfold sdist
  rw [h]

/-- **Existence of the spherical nine-point circle.**  Given a spherical triangle with
vertices `A, B, C` whose sides are non-degenerate (no two endpoints antipodal), its three
side-midpoints `sMidpoint B C`, `sMidpoint A C`, `sMidpoint A B` — the medial triangle — lie
on a common spherical circle `sCircle O ρ`.  This is the spherical nine-point circle,
obtained by feeding the medial triangle to the merged circumcircle primitive
`sphericalCircumcircle_exists`. -/
theorem sphericalNinePointCircle_exists [FiniteDimensional ℝ E]
    (A B C : E) (hBC : B + C ≠ 0) (hAC : A + C ≠ 0) (hAB : A + B ≠ 0)
    (hdim : 2 < Module.finrank ℝ E) :
    ∃ (O : E) (ρ : ℝ), OnSphere O ∧
      sMidpoint B C ∈ sCircle O ρ ∧ sMidpoint A C ∈ sCircle O ρ ∧
      sMidpoint A B ∈ sCircle O ρ :=
  sphericalCircumcircle_exists (sMidpoint B C) (sMidpoint A C) (sMidpoint A B)
    (onSphere_sMidpoint hBC) (onSphere_sMidpoint hAC) (onSphere_sMidpoint hAB) hdim

end FeuerbachsTheoremOQ04
