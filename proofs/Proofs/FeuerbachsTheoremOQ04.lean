/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): spherical model foundations

This file gives the gallery problem `feuerbachs-theorem-oq-04`
("Feuerbach's Theorem in Non-Euclidean Geometry") a concrete formal grounding and a
first layer of **verified** foundational lemmas.  The parent problem was a fresh stub
with `problemStatement.formal = "(formal statement to be added)"`; this file supplies a
precise statement target and the metric primitives any non-Euclidean tangency argument
needs, all `0`-axiom / `0`-sorry.

## Why the spherical model (and not hyperbolic)

The classical Feuerbach theorem (the nine-point circle is tangent to the incircle and the
three excircles) has analogues in both constant-curvature non-Euclidean geometries.  Of
the two, only the **spherical** model has a clean, axiom-free realisation in current
Mathlib: a point of the unit sphere `Sⁿ ⊆ E` is just a unit vector of a real inner-product
space `E`, and the geodesic (spherical) distance between unit vectors `P, Q` is the angle
they subtend, `Real.arccos ⟪P, Q⟫`.  Mathlib's hyperbolic-geometry support is far thinner
(no developed hyperboloid / Poincaré-disk metric), so a hyperbolic formalisation would have
to build the model from scratch — out of scope for a single session and prone to becoming
scaffolding on unverified axioms.  We therefore anchor this problem in the spherical model,
where every primitive below is a theorem about Mathlib's existing `InnerProductSpace ℝ E`.

## Formal statement target (documented; not claimed here)

In the spherical model a **spherical circle** with centre `O` (a unit vector) and angular
radius `ρ ∈ (0, π)` is the level set `{P : OnSphere P ∧ scos P O = Real.cos ρ}`.  Two such
circles `(O₁, ρ₁)`, `(O₂, ρ₂)` are *internally tangent* when they meet in exactly one point
and one contains the other, which (for the sphere) happens iff the spherical distance
between centres satisfies `sdist O₁ O₂ = |ρ₁ − ρ₂|`; *externally tangent* iff
`sdist O₁ O₂ = ρ₁ + ρ₂`.  The spherical Feuerbach statement is then: for a spherical
triangle, the spherical nine-point circle is tangent (in this sense) to the spherical
incircle and the three excircles.  Reaching it requires a spherical incircle/nine-point
construction; this file establishes the metric layer underneath that construction.

## What this file proves (0 axioms, 0 sorries)

* `chord_sq` — the **chord–cosine bridge** `‖P − Q‖² = 2 − 2·scos P Q` for unit vectors,
  relating the ambient Euclidean chord to the spherical cosine.  This is the identity that
  lets a tangency condition be checked algebraically in the inner product.
* `abs_scos_le_one`, `scos_le_one`, `neg_one_le_scos` — the spherical cosine lies in
  `[-1, 1]`, so `sdist` is a genuine angle.
* `scos_self`, `sdist_self`, `sdist_nonneg`, `sdist_le_pi`, `sdist_eq_zero_of_eq` — `sdist`
  is a well-defined `[0, π]`-valued quantity vanishing on the diagonal.
-/
import Mathlib

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A point of the spherical model: a unit vector of the ambient real inner-product space. -/
def OnSphere (P : E) : Prop := ‖P‖ = 1

/-- Cosine of the spherical (geodesic) distance between two model points: the inner product. -/
noncomputable def scos (P Q : E) : ℝ := ⟪P, Q⟫

/-- Spherical distance: the angle subtended at the centre, `arccos` of the inner product. -/
noncomputable def sdist (P Q : E) : ℝ := Real.arccos ⟪P, Q⟫

/-- **Chord–cosine bridge.**  For unit vectors the squared ambient chord length is
`2 − 2·cos(spherical distance)`.  This is the algebraic handle that turns a spherical
tangency condition into an inner-product equation. -/
theorem chord_sq (P Q : E) (hP : OnSphere P) (hQ : OnSphere Q) :
    ‖P - Q‖ ^ 2 = 2 - 2 * scos P Q := by
  have expand : ⟪P - Q, P - Q⟫ = ‖P‖ ^ 2 - 2 * ⟪P, Q⟫ + ‖Q‖ ^ 2 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm Q P]
    ring
  rw [← real_inner_self_eq_norm_sq, expand, hP, hQ, scos]
  ring

/-- The spherical cosine is bounded by `1` in absolute value (Cauchy–Schwarz on unit
vectors), so `sdist` is the `arccos` of a genuine cosine value. -/
theorem abs_scos_le_one (P Q : E) (hP : OnSphere P) (hQ : OnSphere Q) :
    |scos P Q| ≤ 1 := by
  have h := abs_real_inner_le_norm P Q
  rw [hP, hQ] at h
  simpa [scos] using h

/-- The spherical cosine is at most `1`. -/
theorem scos_le_one (P Q : E) (hP : OnSphere P) (hQ : OnSphere Q) :
    scos P Q ≤ 1 :=
  (abs_le.mp (abs_scos_le_one P Q hP hQ)).2

/-- The spherical cosine is at least `-1`. -/
theorem neg_one_le_scos (P Q : E) (hP : OnSphere P) (hQ : OnSphere Q) :
    -1 ≤ scos P Q :=
  (abs_le.mp (abs_scos_le_one P Q hP hQ)).1

/-- A model point has spherical cosine `1` with itself. -/
theorem scos_self (P : E) (hP : OnSphere P) : scos P P = 1 := by
  rw [scos, real_inner_self_eq_norm_sq, hP]; norm_num

/-- The spherical distance from a point to itself is `0`. -/
theorem sdist_self (P : E) (hP : OnSphere P) : sdist P P = 0 := by
  rw [sdist, show (⟪P, P⟫ : ℝ) = 1 from by rw [real_inner_self_eq_norm_sq, hP]; norm_num,
    Real.arccos_one]

/-- Spherical distance is nonnegative. -/
theorem sdist_nonneg (P Q : E) : 0 ≤ sdist P Q := Real.arccos_nonneg _

/-- Spherical distance is at most `π` (antipodal points). -/
theorem sdist_le_pi (P Q : E) : sdist P Q ≤ Real.pi := Real.arccos_le_pi _

/-- Equal model points are at spherical distance `0`. -/
theorem sdist_eq_zero_of_eq {P Q : E} (hP : OnSphere P) (h : P = Q) : sdist P Q = 0 := by
  subst h; exact sdist_self P hP

end FeuerbachsTheoremOQ04
