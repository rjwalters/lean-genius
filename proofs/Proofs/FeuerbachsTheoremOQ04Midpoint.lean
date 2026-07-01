/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): the spherical midpoint layer

This companion file to `Proofs.FeuerbachsTheoremOQ04` adds the **spherical midpoint** of two
model points and proves that it genuinely bisects the geodesic arc joining them.

Why this matters for Feuerbach: the classical nine-point circle passes through the three
**midpoints of the triangle's sides**.  Any spherical nine-point construction therefore needs
a verified notion of "the midpoint of a spherical segment" — a model point `M` on the shorter
geodesic from `P` to `Q` that is equidistant from both, with `sdist P M = sdist P Q / 2`.
This file supplies exactly that primitive, `0`-axiom / `0`-sorry, building only on the
*merged* metric API of `Proofs.FeuerbachsTheoremOQ04` (`OnSphere`, `scos`, `sdist`).  It is
deliberately orthogonal to the incircle / incenter / bisector layers so it does not touch the
shared `FeuerbachsTheoremOQ04.lean` file.

## Construction

For non-antipodal unit vectors `P, Q` (equivalently `scos P Q > -1`, so `P + Q ≠ 0`) the
spherical midpoint is the **normalised sum**

    sMidpoint P Q := ‖P + Q‖⁻¹ • (P + Q).

This is the point where the perpendicular bisector plane of the chord `PQ` meets the sphere on
the near side.  The one nontrivial computation is the half-angle identity
`⟪P, sMidpoint P Q⟫ = cos ((arccos (scos P Q)) / 2)`, which turns "the inner product of `P`
with the midpoint" into "the cosine of half the spherical distance" via `Real.cos_half`.

## What this file proves (0 axioms, 0 sorries)

* `norm_add_sq_onSphere` — `‖P + Q‖² = 2 + 2·scos P Q` for unit vectors (the addition analogue
  of the merged `chord_sq`).
* `norm_add_pos` — for non-antipodal points `‖P + Q‖ > 0`, so the midpoint is well defined.
* `onSphere_sMidpoint` — the midpoint is again a model point (unit norm).
* `sMidpoint_comm`, `scos_comm` — symmetry of the construction and of `scos`.
* `inner_sMidpoint_left`, `inner_sMidpoint_right` — the inner product of the midpoint with each
  endpoint equals `‖P + Q‖⁻¹ · (1 + scos P Q)`; in particular the two are equal.
* `scos_sMidpoint_equidist`, `sdist_sMidpoint_equidist` — the midpoint is **equidistant** from
  the two endpoints.
* `sdist_sMidpoint_bisect` (headline) — `sdist P (sMidpoint P Q) = sdist P Q / 2`: the midpoint
  lies at exactly half the spherical distance from `P`.
* `sdist_sMidpoint_right` — the symmetric `sdist Q (sMidpoint P Q) = sdist P Q / 2`.
* `sdist_sMidpoint_add` — `sdist P M + sdist M Q = sdist P Q`: the midpoint lies **on** the
  geodesic segment from `P` to `Q` (the triangle inequality holds with equality), i.e. it is a
  genuine arc midpoint, not merely an equidistant point.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Sum–cosine bridge.**  For unit vectors the squared ambient length of `P + Q` is
`2 + 2·cos(spherical distance)` — the addition analogue of `chord_sq`. -/
theorem norm_add_sq_onSphere {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    ‖P + Q‖ ^ 2 = 2 + 2 * scos P Q := by
  have expand : ⟪P + Q, P + Q⟫ = ‖P‖ ^ 2 + 2 * ⟪P, Q⟫ + ‖Q‖ ^ 2 := by
    rw [inner_add_left, inner_add_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm Q P]
    ring
  rw [← real_inner_self_eq_norm_sq, expand, hP, hQ, scos]
  ring

/-- Spherical cosine is symmetric (the inner product is). -/
theorem scos_comm (P Q : E) : scos P Q = scos Q P := by
  unfold scos; exact real_inner_comm P Q

/-- For **non-antipodal** model points (`scos P Q > -1`) the sum `P + Q` is nonzero, so the
normalised sum below is well defined. -/
theorem norm_add_pos {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q)
    (hlt : (-1 : ℝ) < scos P Q) : 0 < ‖P + Q‖ := by
  have hsq : ‖P + Q‖ ^ 2 = 2 + 2 * scos P Q := norm_add_sq_onSphere hP hQ
  have hpos : (0 : ℝ) < ‖P + Q‖ ^ 2 := by rw [hsq]; linarith
  nlinarith [norm_nonneg (P + Q), hpos]

/-- The **spherical midpoint** of two model points: the renormalised sum.  For non-antipodal
`P, Q` this is the point of the sphere on the perpendicular bisector plane of the chord `PQ`
that lies on the shorter geodesic between them. -/
noncomputable def sMidpoint (P Q : E) : E := (‖P + Q‖)⁻¹ • (P + Q)

/-- The spherical midpoint is symmetric in its two endpoints. -/
theorem sMidpoint_comm (P Q : E) : sMidpoint P Q = sMidpoint Q P := by
  unfold sMidpoint; rw [add_comm P Q]

/-- The spherical midpoint of two model points is again a model point (unit norm). -/
theorem onSphere_sMidpoint {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q)
    (hlt : (-1 : ℝ) < scos P Q) : OnSphere (sMidpoint P Q) := by
  have hpos := norm_add_pos hP hQ hlt
  unfold OnSphere sMidpoint
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hpos)]

/-- Inner product of the midpoint with the **first** endpoint: `‖P + Q‖⁻¹ · (1 + scos P Q)`. -/
theorem inner_sMidpoint_left {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    (⟪sMidpoint P Q, P⟫ : ℝ) = (‖P + Q‖)⁻¹ * (1 + scos P Q) := by
  unfold sMidpoint
  rw [real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hP, real_inner_comm Q P]
  simp only [scos]
  ring

/-- Inner product of the midpoint with the **second** endpoint: `‖P + Q‖⁻¹ · (scos P Q + 1)`. -/
theorem inner_sMidpoint_right {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    (⟪sMidpoint P Q, Q⟫ : ℝ) = (‖P + Q‖)⁻¹ * (scos P Q + 1) := by
  unfold sMidpoint
  rw [real_inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hQ]
  simp only [scos]
  ring

/-- The midpoint has the **same spherical cosine** with each endpoint — the algebraic form of
"equidistant from both". -/
theorem scos_sMidpoint_equidist {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    scos (sMidpoint P Q) P = scos (sMidpoint P Q) Q := by
  rw [scos, scos, inner_sMidpoint_left hP hQ, inner_sMidpoint_right hP hQ]
  ring

/-- The midpoint is **equidistant** from the two endpoints (in spherical distance). -/
theorem sdist_sMidpoint_equidist {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    sdist (sMidpoint P Q) P = sdist (sMidpoint P Q) Q := by
  unfold sdist
  rw [inner_sMidpoint_left hP hQ, inner_sMidpoint_right hP hQ]
  congr 1
  ring

/-- **Headline: the spherical midpoint bisects the geodesic arc.**  For non-antipodal model
points the spherical distance from `P` to `sMidpoint P Q` is exactly half the spherical
distance from `P` to `Q`.

The engine is the half-angle identity `⟪P, sMidpoint P Q⟫ = cos ((arccos (scos P Q)) / 2)`:
the inner product of `P` with the midpoint equals the cosine of half the angle `∠POQ`. -/
theorem sdist_sMidpoint_bisect {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q)
    (hlt : (-1 : ℝ) < scos P Q) :
    sdist P (sMidpoint P Q) = sdist P Q / 2 := by
  have hs_hi : scos P Q ≤ 1 := scos_le_one P Q hP hQ
  have hpos := norm_add_pos hP hQ hlt
  have h1s : (0 : ℝ) < 1 + scos P Q := by linarith
  -- inner product of `P` with the midpoint
  have hIM : (⟪P, sMidpoint P Q⟫ : ℝ) = (‖P + Q‖)⁻¹ * (1 + scos P Q) := by
    rw [real_inner_comm P (sMidpoint P Q), inner_sMidpoint_left hP hQ]
  have hnn : 0 ≤ (⟪P, sMidpoint P Q⟫ : ℝ) := by
    rw [hIM]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (by linarith)
  have hns : ‖P + Q‖ ^ 2 = 2 + 2 * scos P Q := norm_add_sq_onSphere hP hQ
  have h1s' : (1 + scos P Q) ≠ 0 := ne_of_gt h1s
  -- the square of that inner product is `(1 + scos P Q) / 2`
  have hsq : (⟪P, sMidpoint P Q⟫ : ℝ) ^ 2 = (1 + scos P Q) / 2 := by
    rw [hIM, mul_pow, inv_pow, hns,
      show (2 : ℝ) + 2 * scos P Q = 2 * (1 + scos P Q) from by ring]
    field_simp
    ring
  -- half-angle identity: the inner product is `cos ((arccos (scos P Q)) / 2)`
  have hval : (⟪P, sMidpoint P Q⟫ : ℝ) = Real.cos (Real.arccos (scos P Q) / 2) := by
    rw [Real.cos_half (by linarith [Real.arccos_nonneg (scos P Q), Real.pi_pos])
        (Real.arccos_le_pi (scos P Q)),
      Real.cos_arccos (le_of_lt hlt) hs_hi, ← Real.sqrt_sq hnn, hsq]
  -- assemble: `sdist P M = arccos (cos (arccos (scos P Q) / 2)) = arccos (scos P Q) / 2`
  have hsdM : sdist P (sMidpoint P Q) = Real.arccos (⟪P, sMidpoint P Q⟫) := rfl
  have hsdPQ : sdist P Q = Real.arccos (scos P Q) := rfl
  rw [hsdM, hval,
    Real.arccos_cos (by linarith [Real.arccos_nonneg (scos P Q)])
      (by linarith [Real.arccos_le_pi (scos P Q), Real.pi_pos]),
    hsdPQ]

/-- Symmetric form of the bisection: the midpoint is also at half the distance from `Q`. -/
theorem sdist_sMidpoint_right {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q)
    (hlt : (-1 : ℝ) < scos P Q) :
    sdist Q (sMidpoint P Q) = sdist P Q / 2 := by
  have hlt' : (-1 : ℝ) < scos Q P := by rw [scos_comm Q P]; exact hlt
  rw [sMidpoint_comm, sdist_sMidpoint_bisect hQ hP hlt', sdist_comm Q P]

/-- **The midpoint lies on the geodesic segment.**  Its two half-distances add back to the full
spherical distance, so the triangle inequality holds with equality — `sMidpoint P Q` is a
genuine arc midpoint, not merely an equidistant point off the geodesic. -/
theorem sdist_sMidpoint_add {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q)
    (hlt : (-1 : ℝ) < scos P Q) :
    sdist P (sMidpoint P Q) + sdist (sMidpoint P Q) Q = sdist P Q := by
  rw [sdist_sMidpoint_bisect hP hQ hlt, sdist_comm (sMidpoint P Q) Q,
    sdist_sMidpoint_right hP hQ hlt]
  ring

end FeuerbachsTheoremOQ04
