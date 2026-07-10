/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): the tangent great circle at a point

This companion file to `Proofs.FeuerbachsTheoremOQ04` supplies the **tangent great circle to a
spherical small circle at a prescribed point on it**.  The merged file already has the
*converse* direction — given a great circle tangent to a small circle, `greatCircleFoot`
locates the contact point (`circle_tangent_greatCircle_inter`).  Here we go the other way:
given a point `P` on the small circle `sCircle O ρ`, we construct the (unique) great circle
that touches the small circle at `P`, and prove it meets the small circle *only* at `P`.

## Why this matters for Feuerbach

The mechanism of the classical Feuerbach theorem is a **common tangent line** at a point of
contact.  On the sphere, "tangent line" is "tangent great circle", so before one can talk
about a common tangent one needs, for each point of a circle, the great circle tangent there.
The merged tritangent/incircle machinery describes tangency of a *given* great circle to a
circle (the algebraic criterion `|⟪O,N⟫| = sin ρ`), but never produces the tangent great
circle *at a chosen point*.  This file closes that gap with an explicit construction.

## The construction

Let `P` lie on `sCircle O ρ`, so `⟪P,O⟫ = cos ρ`.  The tangent great circle at `P` is the
great circle through `P` perpendicular to the geodesic `PO` — i.e. the great circle whose pole
points along the **radial direction** `radialDir P O = O − ⟪O,P⟫•P` (the component of the
centre `O` orthogonal to `P`).  That component has norm `sin ρ`, so the unit pole is

  `tangentPole P O ρ = (sin ρ)⁻¹ • (O − ⟪O,P⟫•P)`.

A direct inner-product computation gives, for `0 < ρ < π/2`:

* `⟪tangentPole, tangentPole⟫ = 1` — it is a genuine model pole (`onSphere_tangentPole`);
* `⟪P, tangentPole⟫ = 0` — `P` lies on the great circle `sGreatCircle (tangentPole P O ρ)`;
* `⟪O, tangentPole⟫ = sin ρ`, so `|⟪O,·⟫| = sin ρ` — the great circle **is tangent** to
  `sCircle O ρ` (`tangentToGreatCircle_tangentPole`).

Feeding this tangency into the merged `circle_tangent_greatCircle_inter` shows the small circle
and the great circle meet in exactly one point, and since `P` lies on both, that point is `P`:
the great circle is tangent to `sCircle O ρ` **at `P`** (`tangentGreatCircle_at_point`).

Everything is built on the *merged* API of `Proofs.FeuerbachsTheoremOQ04` (`OnSphere`, `scos`,
`sCircle`, `sGreatCircle`, `radialDir`, `TangentToGreatCircle`, `greatCircleFoot`,
`circle_tangent_greatCircle_inter`, `inner_radialDir`, `inner_orthoComp_self`); this file adds
no axioms and no sorries.

## What this file proves (0 axioms, 0 sorries)

* `tangentPole` — the explicit unit pole `(sin ρ)⁻¹ • radialDir P O` of the tangent great
  circle at a point `P` of `sCircle O ρ`.
* `onSphere_tangentPole` — the pole is a model point (unit vector) for `0 < ρ < π/2`.
* `inner_point_tangentPole` — `⟪P, tangentPole P O ρ⟫ = 0`: `P` lies on the tangent great circle.
* `mem_sGreatCircle_tangentPole` — packaged: `P ∈ sGreatCircle (tangentPole P O ρ)`.
* `inner_center_tangentPole` — `⟪O, tangentPole P O ρ⟫ = sin ρ`.
* `tangentToGreatCircle_tangentPole` — the great circle is tangent to `sCircle O ρ`.
* `tangentGreatCircle_at_point` — **headline**: the tangent great circle at `P` meets
  `sCircle O ρ` in exactly `{P}`, so it is tangent to the small circle precisely at `P`.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The tangent pole at a point of a spherical circle.**  For a point `P` on the small
circle `sCircle O ρ`, the unit pole of the great circle tangent to that circle at `P`: the
normalised radial direction `(sin ρ)⁻¹ • (O − ⟪O,P⟫•P)`.  Its great circle passes through `P`
and touches `sCircle O ρ` there. -/
noncomputable def tangentPole (P O : E) (ρ : ℝ) : E := (Real.sin ρ)⁻¹ • radialDir P O

/-- The radial direction `O − ⟪O,P⟫•P` has squared norm `sin²ρ` when `⟪P,O⟫ = cos ρ` for two
model points — the spherical Pythagoras for the projection of the centre onto the great circle. -/
theorem inner_self_radialDir {O P : E} {ρ : ℝ} (hO : OnSphere O) (hP : OnSphere P)
    (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    (⟪radialDir P O, radialDir P O⟫ : ℝ) = Real.sin ρ ^ 2 := by
  have hOP : (⟪O, P⟫ : ℝ) = Real.cos ρ := by rw [real_inner_comm]; exact hPO
  have h := inner_orthoComp_self (O := O) (N := P) hO hP
  rw [show radialDir P O = O - (⟪O, P⟫ : ℝ) • P from rfl, h, hOP]
  nlinarith [Real.sin_sq_add_cos_sq ρ]

/-- `⟪P, radialDir P O⟫ = 0`: the point `P` is orthogonal to the radial direction, i.e. lies
on the perpendicular great circle. -/
theorem inner_point_radialDir {O P : E} {ρ : ℝ} (hP : OnSphere P)
    (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    (⟪P, radialDir P O⟫ : ℝ) = 0 := by
  have hOP : (⟪O, P⟫ : ℝ) = Real.cos ρ := by rw [real_inner_comm]; exact hPO
  have hPP : (⟪P, P⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, show ‖P‖ = 1 from hP]; norm_num
  rw [inner_radialDir, hPO, hOP, hPP]; ring

/-- `⟪O, radialDir P O⟫ = sin²ρ`: the centre projects onto its own radial direction with the
squared spherical sine. -/
theorem inner_center_radialDir {O P : E} {ρ : ℝ} (hO : OnSphere O)
    (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    (⟪O, radialDir P O⟫ : ℝ) = Real.sin ρ ^ 2 := by
  have hOP : (⟪O, P⟫ : ℝ) = Real.cos ρ := by rw [real_inner_comm]; exact hPO
  have hOO : (⟪O, O⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, show ‖O‖ = 1 from hO]; norm_num
  rw [inner_radialDir, hOO, hOP]
  nlinarith [Real.sin_sq_add_cos_sq ρ]

/-- **The tangent pole is a model point.**  For `0 < ρ < π/2` (a genuine small circle, and `P`
not the centre), the normalised radial direction has unit norm. -/
theorem onSphere_tangentPole {O P : E} {ρ : ℝ} (hO : OnSphere O) (hP : OnSphere P)
    (hρ0 : 0 < ρ) (hρ2 : ρ < Real.pi / 2) (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    OnSphere (tangentPole P O ρ) := by
  have hsinpos : 0 < Real.sin ρ :=
    Real.sin_pos_of_pos_of_lt_pi hρ0 (by linarith [Real.pi_pos])
  have hDD : (⟪radialDir P O, radialDir P O⟫ : ℝ) = Real.sin ρ ^ 2 :=
    inner_self_radialDir hO hP hPO
  have hNN : (⟪tangentPole P O ρ, tangentPole P O ρ⟫ : ℝ) = 1 := by
    unfold tangentPole
    rw [real_inner_smul_left, real_inner_smul_right, hDD]
    field_simp
  have hsqn : ‖tangentPole P O ρ‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact hNN
  have hfac : (‖tangentPole P O ρ‖ - 1) * (‖tangentPole P O ρ‖ + 1) = 0 := by nlinarith [hsqn]
  rcases mul_eq_zero.mp hfac with h | h
  · show ‖tangentPole P O ρ‖ = 1; linarith
  · exact absurd h (by have := norm_nonneg (tangentPole P O ρ); positivity)

/-- **`P` lies on the tangent great circle.**  `⟪P, tangentPole P O ρ⟫ = 0`. -/
theorem inner_point_tangentPole {O P : E} {ρ : ℝ} (hP : OnSphere P)
    (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    (⟪P, tangentPole P O ρ⟫ : ℝ) = 0 := by
  unfold tangentPole
  rw [real_inner_smul_right, inner_point_radialDir hP hPO, mul_zero]

/-- **`P` lies on the tangent great circle (packaged).**  `P ∈ sGreatCircle (tangentPole P O ρ)`. -/
theorem mem_sGreatCircle_tangentPole {O P : E} {ρ : ℝ} (hP : OnSphere P)
    (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    P ∈ sGreatCircle (tangentPole P O ρ) :=
  ⟨hP, inner_point_tangentPole hP hPO⟩

/-- **The centre projects onto the tangent pole with the spherical sine.**
`⟪O, tangentPole P O ρ⟫ = sin ρ`. -/
theorem inner_center_tangentPole {O P : E} {ρ : ℝ} (hO : OnSphere O)
    (hρ0 : 0 < ρ) (hρ2 : ρ < Real.pi / 2) (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    (⟪O, tangentPole P O ρ⟫ : ℝ) = Real.sin ρ := by
  have hsinpos : 0 < Real.sin ρ :=
    Real.sin_pos_of_pos_of_lt_pi hρ0 (by linarith [Real.pi_pos])
  unfold tangentPole
  rw [real_inner_smul_right, inner_center_radialDir hO hPO, pow_two, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt hsinpos), one_mul]

/-- **The tangent great circle is tangent to the small circle.**  `|⟪O, tangentPole P O ρ⟫| =
sin ρ`, the algebraic tangency criterion `TangentToGreatCircle O ρ (tangentPole P O ρ)`. -/
theorem tangentToGreatCircle_tangentPole {O P : E} {ρ : ℝ} (hO : OnSphere O)
    (hρ0 : 0 < ρ) (hρ2 : ρ < Real.pi / 2) (hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ) :
    TangentToGreatCircle O ρ (tangentPole P O ρ) := by
  have hsinpos : 0 < Real.sin ρ :=
    Real.sin_pos_of_pos_of_lt_pi hρ0 (by linarith [Real.pi_pos])
  unfold TangentToGreatCircle
  rw [inner_center_tangentPole hO hρ0 hρ2 hPO, abs_of_pos hsinpos]

/-- **The tangent great circle at a point of a spherical circle.**  For a point `P` on the
small circle `sCircle O ρ` (with `0 < ρ < π/2`), the great circle with pole `tangentPole P O ρ`
passes through `P`, is tangent to `sCircle O ρ`, and meets `sCircle O ρ` in *exactly* the point
`P`.  This is the point-wise tangent-line primitive underneath any spherical Feuerbach argument:
it turns "a point of a circle" into "the great circle tangent there", dual to the merged
`circle_tangent_greatCircle_inter` (which turns a tangent great circle into its contact foot). -/
theorem tangentGreatCircle_at_point {O P : E} {ρ : ℝ} (hO : OnSphere O) (hρ0 : 0 < ρ)
    (hρ2 : ρ < Real.pi / 2) (hPcirc : P ∈ sCircle O ρ) :
    OnSphere (tangentPole P O ρ) ∧
      P ∈ sGreatCircle (tangentPole P O ρ) ∧
      TangentToGreatCircle O ρ (tangentPole P O ρ) ∧
      sCircle O ρ ∩ sGreatCircle (tangentPole P O ρ) = {P} := by
  obtain ⟨hP, hPscos⟩ := hPcirc
  have hPO : (⟪P, O⟫ : ℝ) = Real.cos ρ := hPscos
  have hN : OnSphere (tangentPole P O ρ) := onSphere_tangentPole hO hP hρ0 hρ2 hPO
  have hPgc : P ∈ sGreatCircle (tangentPole P O ρ) := mem_sGreatCircle_tangentPole hP hPO
  have htan : TangentToGreatCircle O ρ (tangentPole P O ρ) :=
    tangentToGreatCircle_tangentPole hO hρ0 hρ2 hPO
  refine ⟨hN, hPgc, htan, ?_⟩
  have hinter := circle_tangent_greatCircle_inter hO hN (le_of_lt hρ0) hρ2 htan
  have hPin : P ∈ sCircle O ρ ∩ sGreatCircle (tangentPole P O ρ) := ⟨⟨hP, hPscos⟩, hPgc⟩
  rw [hinter] at hPin
  rw [Set.mem_singleton_iff] at hPin
  rw [hinter, hPin]

end FeuerbachsTheoremOQ04
