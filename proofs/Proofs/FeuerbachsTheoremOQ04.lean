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
* `scos_eq_one_iff`, `sdist_eq_zero_iff`, `sdist_pos` — **point separation**: for unit
  vectors `sdist P Q = 0 ↔ P = Q`, so together with symmetry and nonnegativity `sdist`
  separates points.
* `sdist_eq_angle`, `sdist_triangle`, `sdist_isMetric` — the **spherical triangle
  inequality** and metric capstone: identifying `sdist` with Mathlib's unoriented angle
  transports `angle_le_angle_add_angle` to `sdist P R ≤ sdist P Q + sdist Q R`, completing
  all four metric-space axioms — `(Sⁿ, sdist)` is a genuine metric on the spherical model.
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

/-- Spherical distance is symmetric (the inner product commutes). -/
theorem sdist_comm (P Q : E) : sdist P Q = sdist Q P := by
  unfold sdist; rw [real_inner_comm]

/-- **Spherical cosine `1` characterises equality.**  For unit vectors `P, Q`, the chord
`‖P − Q‖² = 2 − 2·scos P Q` (`chord_sq`) vanishes exactly when `scos P Q = 1`, i.e. exactly
when `P = Q`.  This is the algebraic heart of point separation. -/
theorem scos_eq_one_iff {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    scos P Q = 1 ↔ P = Q := by
  refine ⟨fun h => ?_, fun h => h ▸ scos_self P hP⟩
  have hsq : ‖P - Q‖ ^ 2 = 0 := by rw [chord_sq P Q hP hQ, h]; ring
  have hz : ‖P - Q‖ = 0 := by
    have hnn := norm_nonneg (P - Q)
    have hle : ‖P - Q‖ ≤ 0 := by nlinarith [hsq, hnn]
    linarith
  rw [norm_eq_zero, sub_eq_zero] at hz
  exact hz

/-- **Point separation.**  For unit vectors, spherical distance `0` characterises equality.
Combined with `sdist_self` (vanishing on the diagonal), `sdist_nonneg`, and `sdist_comm`
(symmetry), this shows `sdist` separates points, so it is a genuine metric on the spherical
model — only the spherical triangle inequality remains to make `(Sⁿ, sdist)` a metric
space.  Proof: `arccos` of the inner product is `0` iff that inner product is `≥ 1`, which
for unit vectors forces `scos P Q = 1`, hence `P = Q` by `scos_eq_one_iff`. -/
theorem sdist_eq_zero_iff {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    sdist P Q = 0 ↔ P = Q := by
  rw [sdist, Real.arccos_eq_zero]
  constructor
  · intro h
    exact (scos_eq_one_iff hP hQ).mp (le_antisymm (scos_le_one P Q hP hQ) h)
  · intro h
    have h1 : scos P Q = 1 := (scos_eq_one_iff hP hQ).mpr h
    rw [scos] at h1
    exact h1.ge

/-- Distinct model points are at strictly positive spherical distance. -/
theorem sdist_pos {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) (hPQ : P ≠ Q) :
    0 < sdist P Q :=
  lt_of_le_of_ne (sdist_nonneg P Q) fun h => hPQ ((sdist_eq_zero_iff hP hQ).mp h.symm)

/-- **Cosine of the spherical distance is the spherical cosine.**  Since
`sdist P Q = arccos (scos P Q)` and the spherical cosine lies in `[-1, 1]` for unit
vectors, applying `cos` recovers it.  This is the everyday bridge `cos (sdist) = scos`
used to move between the metric (`sdist`) and algebraic (`scos`, hence inner product)
descriptions of a configuration. -/
theorem cos_sdist (P Q : E) (hP : OnSphere P) (hQ : OnSphere Q) :
    Real.cos (sdist P Q) = scos P Q := by
  rw [sdist, scos]
  exact Real.cos_arccos (neg_one_le_scos P Q hP hQ) (scos_le_one P Q hP hQ)

/-- **`sdist` is Mathlib's unoriented vector angle.**  Mathlib defines
`InnerProductGeometry.angle P Q = arccos (⟪P, Q⟫ / (‖P‖·‖Q‖))`; for unit vectors the
normalising factor `‖P‖·‖Q‖` is `1`, so it collapses to `arccos ⟪P, Q⟫ = sdist P Q`.  This
bridge lets the spherical metric inherit Mathlib's developed angle theory — in particular
the angle triangle inequality, which becomes the spherical triangle inequality below. -/
theorem sdist_eq_angle {P Q : E} (hP : OnSphere P) (hQ : OnSphere Q) :
    sdist P Q = InnerProductGeometry.angle P Q := by
  rw [sdist, InnerProductGeometry.angle, hP, hQ]
  norm_num

/-- **Spherical triangle inequality.**  For model points (unit vectors),
`sdist P R ≤ sdist P Q + sdist Q R`.  This is the final metric-space axiom: combined with
`sdist_self` (vanishing on the diagonal), `sdist_eq_zero_iff` (point separation),
`sdist_nonneg`, and `sdist_comm` (symmetry), it makes `(Sⁿ, sdist)` a genuine metric space.
The proof transports Mathlib's `InnerProductGeometry.angle_le_angle_add_angle` along the
identification `sdist_eq_angle`. -/
theorem sdist_triangle {P Q R : E} (hP : OnSphere P) (hQ : OnSphere Q) (hR : OnSphere R) :
    sdist P R ≤ sdist P Q + sdist Q R := by
  rw [sdist_eq_angle hP hR, sdist_eq_angle hP hQ, sdist_eq_angle hQ hR]
  exact InnerProductGeometry.angle_le_angle_add_angle P Q R

/-- **`sdist` is a genuine metric on the spherical model.**  All four metric-space axioms
hold for `sdist` restricted to model points (unit vectors): it vanishes on the diagonal,
separates points, is symmetric, and satisfies the triangle inequality.  Packaging this as a
bundled `MetricSpace` instance would only additionally require carving the sphere out as a
subtype; the mathematical content — the axioms themselves — is exactly this conjunction. -/
theorem sdist_isMetric :
    (∀ P : E, OnSphere P → sdist P P = 0) ∧
    (∀ P Q : E, OnSphere P → OnSphere Q → (sdist P Q = 0 ↔ P = Q)) ∧
    (∀ P Q : E, sdist P Q = sdist Q P) ∧
    (∀ P Q R : E, OnSphere P → OnSphere Q → OnSphere R →
      sdist P R ≤ sdist P Q + sdist Q R) :=
  ⟨fun P hP => sdist_self P hP,
   fun _ _ hP hQ => sdist_eq_zero_iff hP hQ,
   fun P Q => sdist_comm P Q,
   fun _ _ _ hP hQ hR => sdist_triangle hP hQ hR⟩

/-! ## Spherical circles and tangency

With the metric layer in place we can define the basic objects a spherical Feuerbach
argument manipulates: spherical circles as level sets of `scos`, and the spherical
internal/external tangency relations on their centres and angular radii.  The key lemma
`mem_sCircle_iff_sdist` shows the algebraic level-set definition coincides with the
metric "set of points at spherical distance `ρ` from the centre", so the two views are
interchangeable in tangency calculations. -/

/-- A **spherical circle** with centre `O` (a model point) and angular radius `ρ`:
the level set of the spherical cosine, `{P : OnSphere P ∧ scos P O = cos ρ}`.  For
`ρ ∈ [0, π]` this is exactly the set of model points at spherical distance `ρ` from `O`
(`mem_sCircle_iff_sdist`). -/
def sCircle (O : E) (ρ : ℝ) : Set E := {P | OnSphere P ∧ scos P O = Real.cos ρ}

/-- **The level-set circle is the metric circle.**  For a centre `O` on the sphere and
an angular radius `ρ ∈ [0, π]`, a model point `P` lies on `sCircle O ρ` exactly when its
spherical distance to `O` is `ρ`.  This identifies the algebraic definition (a level set
of the inner product) with the geometric one (a sphere of fixed spherical radius). -/
theorem mem_sCircle_iff_sdist {O : E} (hO : OnSphere O) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρπ : ρ ≤ Real.pi) (P : E) :
    P ∈ sCircle O ρ ↔ (OnSphere P ∧ sdist P O = ρ) := by
  simp only [sCircle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, hcos⟩
    refine ⟨hP, ?_⟩
    have hs : sdist P O = Real.arccos (scos P O) := rfl
    rw [hs, hcos]
    exact Real.arccos_cos hρ0 hρπ
  · rintro ⟨hP, hd⟩
    exact ⟨hP, by rw [← cos_sdist P O hP hO, hd]⟩

/-- Two spherical circles `(O₁, ρ₁)` and `(O₂, ρ₂)` are **internally tangent** when the
spherical distance between their centres equals the absolute difference of their angular
radii — the non-Euclidean analogue of the Euclidean `d = |r₁ − r₂|`. -/
def InternallyTangent (O₁ : E) (ρ₁ : ℝ) (O₂ : E) (ρ₂ : ℝ) : Prop :=
  sdist O₁ O₂ = |ρ₁ - ρ₂|

/-- Two spherical circles `(O₁, ρ₁)` and `(O₂, ρ₂)` are **externally tangent** when the
spherical distance between their centres equals the sum of their angular radii — the
non-Euclidean analogue of the Euclidean `d = r₁ + r₂`. -/
def ExternallyTangent (O₁ : E) (ρ₁ : ℝ) (O₂ : E) (ρ₂ : ℝ) : Prop :=
  sdist O₁ O₂ = ρ₁ + ρ₂

/-- Internal tangency is symmetric in the two circles. -/
theorem internallyTangent_comm (O₁ : E) (ρ₁ : ℝ) (O₂ : E) (ρ₂ : ℝ) :
    InternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ InternallyTangent O₂ ρ₂ O₁ ρ₁ := by
  unfold InternallyTangent
  rw [sdist_comm, abs_sub_comm]

/-- External tangency is symmetric in the two circles. -/
theorem externallyTangent_comm (O₁ : E) (ρ₁ : ℝ) (O₂ : E) (ρ₂ : ℝ) :
    ExternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ ExternallyTangent O₂ ρ₂ O₁ ρ₁ := by
  unfold ExternallyTangent
  rw [sdist_comm, add_comm]

/-! ## The tangent point of two externally tangent circles

The defining geometric content of tangency is that the two circles actually **meet** — at
the point on the geodesic joining the centres, at angular distance `ρ₁` from `O₁` (hence
`ρ₂` from `O₂`).  For externally tangent circles with `0 < ρ₁ + ρ₂ < π` we construct that
point explicitly by spherical interpolation (`slerp`):

  `P = cos ρ₁ · O₁ + (sin ρ₁ / sin(ρ₁+ρ₂)) · (O₂ − cos(ρ₁+ρ₂) · O₁)`,

and verify it is a model point lying on **both** circles.  The second summand is the unit
tangent at `O₁` pointing toward `O₂`; the coefficients are exactly the spherical law that
sends `P` an arc `ρ₁` along the geodesic.  This is the construction-heavy crux underneath
any tangency conclusion (and ultimately the spherical Feuerbach statement). -/

/-- **Existence of the tangent point (external case).**  Two externally tangent spherical
circles `(O₁, ρ₁)`, `(O₂, ρ₂)` with `0 < ρ₁ + ρ₂ < π` have a common point — the spherical
interpolation point at arc `ρ₁` from `O₁` along the geodesic to `O₂`. -/
theorem externallyTangent_has_common_point {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : ExternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hpos : 0 < ρ₁ + ρ₂) (hlt : ρ₁ + ρ₂ < Real.pi) :
    ∃ P : E, P ∈ sCircle O₁ ρ₁ ∧ P ∈ sCircle O₂ ρ₂ := by
  set c : ℝ := ⟪O₁, O₂⟫ with hc_def
  set s : ℝ := Real.sin (ρ₁ + ρ₂) with hs_def
  -- unit-vector self-inner products
  have hO₁O₁ : (⟪O₁, O₁⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have hO₂O₂ : (⟪O₂, O₂⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, h₂]; norm_num
  -- cos / sin of the centre distance
  have hcos : Real.cos (ρ₁ + ρ₂) = c := by
    have h := cos_sdist O₁ O₂ h₁ h₂
    rw [htan] at h
    rw [h]; rfl
  have hspos : 0 < s := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s ^ 2 = 1 - c ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (ρ₁ + ρ₂)
    rw [hcos] at h; linarith
  -- the spherical interpolation point
  set P : E := Real.cos ρ₁ • O₁ + (Real.sin ρ₁ / s) • (O₂ - c • O₁) with hP_def
  -- the inner product commutes (folded to c)
  have hc21 : (⟪O₂, O₁⟫ : ℝ) = c := (real_inner_comm O₂ O₁).symm
  -- orthogonality and norm of the tangent vector W = O₂ - c • O₁
  have hW1 : (⟪O₁, O₂ - c • O₁⟫ : ℝ) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hO₁O₁]; ring
  have hW1' : (⟪O₂ - c • O₁, O₁⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact hW1
  have hWW : (⟪O₂ - c • O₁, O₂ - c • O₁⟫ : ℝ) = s ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hc21, hO₁O₁, hO₂O₂]
    rw [hs2]; ring
  -- P is a model point
  have hPP : (⟪P, P⟫ : ℝ) = 1 := by
    have e : (⟪P, P⟫ : ℝ)
        = Real.cos ρ₁ ^ 2 * ⟪O₁, O₁⟫
          + 2 * (Real.cos ρ₁ * (Real.sin ρ₁ / s)) * ⟪O₁, O₂ - c • O₁⟫
          + (Real.sin ρ₁ / s) ^ 2 * ⟪O₂ - c • O₁, O₂ - c • O₁⟫ := by
      rw [hP_def]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm (O₂ - c • O₁) O₁]
      ring
    rw [e, hO₁O₁, hW1, hWW]
    have hss : (Real.sin ρ₁ / s) ^ 2 * s ^ 2 = Real.sin ρ₁ ^ 2 := by field_simp
    linear_combination hss + Real.sin_sq_add_cos_sq ρ₁
  have hP_sphere : OnSphere P := by
    have hsq : ‖P‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hPP
    have hfac : (‖P‖ - 1) * (‖P‖ + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hfac with h | h
    · show ‖P‖ = 1; linarith
    · exact absurd h (by have := norm_nonneg P; positivity)
  -- P lies on the first circle
  have hPO₁ : scos P O₁ = Real.cos ρ₁ := by
    rw [scos, hP_def, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hO₁O₁, hW1']; ring
  -- P lies on the second circle (spherical angle-subtraction)
  have hPO₂ : scos P O₂ = Real.cos ρ₂ := by
    have hsimp : Real.sin ρ₁ / s * s ^ 2 = Real.sin ρ₁ * s := by field_simp
    rw [scos, hP_def, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_sub_left, real_inner_smul_left, hO₂O₂,
      show (1 : ℝ) - c * c = s ^ 2 from by linear_combination -hs2, hsimp,
      show Real.cos ρ₂
          = Real.cos (ρ₁ + ρ₂) * Real.cos ρ₁ + Real.sin (ρ₁ + ρ₂) * Real.sin ρ₁
        from by rw [← Real.cos_sub]; congr 1; ring, hcos, ← hs_def]
    ring
  exact ⟨P, ⟨hP_sphere, hPO₁⟩, ⟨hP_sphere, hPO₂⟩⟩

end FeuerbachsTheoremOQ04
