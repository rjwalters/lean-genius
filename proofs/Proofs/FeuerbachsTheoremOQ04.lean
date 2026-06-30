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

/-! ## The tangent point of two tangent circles

The defining geometric content of tangency is that the two circles actually **meet** — at
the point on the geodesic joining the centres, at angular distance `ρ₁` from `O₁` (hence
`ρ₂` from `O₂`).  We construct that point explicitly by spherical interpolation (`slerp`).
If `d = sdist O₁ O₂ ∈ (0, π)` then

  `P = cos ρ₁ · O₁ + (sin ρ₁ / sin d) · (O₂ − cos d · O₁)`

is the point an arc `ρ₁` along the geodesic from `O₁` toward `O₂` (the second summand is
the unit tangent at `O₁` pointing toward `O₂`).  The core lemma
`sphere_slerp_common_point` shows `P` is a model point with `sdist P O₁ = ρ₁` and, *given
the spherical angle relation* `cos ρ₂ = cos ρ₁ cos d + sin ρ₁ sin d`, also `sdist P O₂ = ρ₂`.
Both the **external** (`d = ρ₁ + ρ₂`) and **internal** (`d = |ρ₁ − ρ₂|`) tangency cases are
then immediate, since each supplies that angle relation by the cosine subtraction formula.
This is the construction-heavy crux underneath any tangency conclusion (and ultimately the
spherical Feuerbach statement). -/

/-- **Spherical slerp common point (core).**  For model points `O₁, O₂` at spherical
distance `d = sdist O₁ O₂ ∈ (0, π)`, and angular radii `ρ₁, ρ₂` related by the spherical
law `cos ρ₂ = cos ρ₁ cos d + sin ρ₁ sin d`, the slerp point at arc `ρ₁` from `O₁` toward
`O₂` lies on both `sCircle O₁ ρ₁` and `sCircle O₂ ρ₂`.  This is the shared engine behind
the external and internal tangent-point existence theorems. -/
theorem sphere_slerp_common_point {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ d : ℝ}
    (hd : sdist O₁ O₂ = d) (hdpos : 0 < d) (hdpi : d < Real.pi)
    (hangle : Real.cos ρ₂ = Real.cos ρ₁ * Real.cos d + Real.sin ρ₁ * Real.sin d) :
    ∃ P : E, P ∈ sCircle O₁ ρ₁ ∧ P ∈ sCircle O₂ ρ₂ := by
  set c : ℝ := Real.cos d with hc_def
  set s : ℝ := Real.sin d with hs_def
  -- unit-vector self-inner products
  have hO₁O₁ : (⟪O₁, O₁⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have hO₂O₂ : (⟪O₂, O₂⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, h₂]; norm_num
  -- the inner product of the two centres is cos d (the spherical cosine), here `c`
  have hcio : (⟪O₁, O₂⟫ : ℝ) = c := by
    have h := cos_sdist O₁ O₂ h₁ h₂
    rw [hd] at h
    rw [hc_def]; exact h.symm
  have hc21 : (⟪O₂, O₁⟫ : ℝ) = c := by rw [real_inner_comm]; exact hcio
  have hspos : 0 < s := Real.sin_pos_of_pos_of_lt_pi hdpos hdpi
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s ^ 2 = 1 - c ^ 2 := by
    have h := Real.sin_sq_add_cos_sq d
    rw [← hc_def, ← hs_def] at h; linarith
  -- the spherical interpolation point
  set P : E := Real.cos ρ₁ • O₁ + (Real.sin ρ₁ / s) • (O₂ - c • O₁) with hP_def
  -- orthogonality and norm of the tangent vector W = O₂ - c • O₁
  have hW1 : (⟪O₁, O₂ - c • O₁⟫ : ℝ) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hcio, hO₁O₁]; ring
  have hW1' : (⟪O₂ - c • O₁, O₁⟫ : ℝ) = 0 := by
    rw [real_inner_comm]; exact hW1
  have hWW : (⟪O₂ - c • O₁, O₂ - c • O₁⟫ : ℝ) = s ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hcio, hc21, hO₁O₁, hO₂O₂]
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
  -- P lies on the second circle (via the spherical angle relation)
  have hPO₂ : scos P O₂ = Real.cos ρ₂ := by
    have hsimp : Real.sin ρ₁ / s * s ^ 2 = Real.sin ρ₁ * s := by field_simp
    rw [scos, hP_def, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_sub_left, real_inner_smul_left, hcio, hO₂O₂,
      show (1 : ℝ) - c * c = s ^ 2 from by linear_combination -hs2, hsimp]
    linear_combination -hangle
  exact ⟨P, ⟨hP_sphere, hPO₁⟩, ⟨hP_sphere, hPO₂⟩⟩

/-- **Existence of the tangent point (external case).**  Two externally tangent spherical
circles `(O₁, ρ₁)`, `(O₂, ρ₂)` with `0 < ρ₁ + ρ₂ < π` have a common point — the spherical
interpolation point at arc `ρ₁` from `O₁` along the geodesic to `O₂`. -/
theorem externallyTangent_has_common_point {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : ExternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hpos : 0 < ρ₁ + ρ₂) (hlt : ρ₁ + ρ₂ < Real.pi) :
    ∃ P : E, P ∈ sCircle O₁ ρ₁ ∧ P ∈ sCircle O₂ ρ₂ :=
  sphere_slerp_common_point h₁ h₂ htan hpos hlt
    (by rw [← Real.cos_sub, show ρ₁ - (ρ₁ + ρ₂) = -ρ₂ from by ring, Real.cos_neg])

/-- **Existence of the tangent point (internal case).**  Two internally tangent spherical
circles `(O₁, ρ₁)`, `(O₂, ρ₂)` with `0 < ρ₁ − ρ₂ < π` (so the second is the smaller, strictly
inside the first) have a common point — again the geodesic interpolation point at arc `ρ₁`
from `O₁` toward `O₂`, which overshoots `O₂` by exactly `ρ₂`. -/
theorem internallyTangent_has_common_point {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : InternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hpos : 0 < ρ₁ - ρ₂) (hlt : ρ₁ - ρ₂ < Real.pi) :
    ∃ P : E, P ∈ sCircle O₁ ρ₁ ∧ P ∈ sCircle O₂ ρ₂ := by
  have hd : sdist O₁ O₂ = ρ₁ - ρ₂ := by rw [htan]; exact abs_of_pos hpos
  exact sphere_slerp_common_point h₁ h₂ hd hpos hlt
    (by rw [← Real.cos_sub]; congr 1; ring)

/-! ## Uniqueness of the tangent point

Existence of a common point (above) is only half of tangency; the geometric heart of the
word *tangent* is that the two circles meet in **exactly one** point.  On the sphere this is
not automatic from the metric data alone — in dimension `≥ 3` two generic spherical circles
meet in a whole `(n−3)`-sphere — and it is precisely the spherical angle relation
`cos ρ₂ = cos ρ₁ cos d + sin ρ₁ sin d` (equivalently the tangency condition on the centres)
that collapses the intersection to a single point.

The mechanism: writing the slerp point as
`Pₛ = cos ρ₁ • O₁ + (sin ρ₁ / sin d) • (O₂ − cos d • O₁)`, *any* common point `Q` has
`⟪Q, Pₛ⟫ = cos²ρ₁ + sin²ρ₁ = 1` (the angle relation supplies the cross term), so
`‖Q − Pₛ‖² = ⟪Q,Q⟫ − 2⟪Q,Pₛ⟫ + ⟪Pₛ,Pₛ⟫ = 1 − 2 + 1 = 0`, forcing `Q = Pₛ`.  Hence the full
intersection is the singleton `{Pₛ}`. -/

/-- **Spherical slerp intersection is a singleton (core).**  Under the same hypotheses as
`sphere_slerp_common_point`, the intersection `sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂` is not merely
nonempty but a single point: the slerp point at arc `ρ₁` from `O₁` toward `O₂`.  This upgrades
existence to genuine tangency — a unique point of contact.  As that point is a linear
combination of the two centres, it additionally lies on `Submodule.span ℝ {O₁, O₂}`: the
geodesic (great circle) through `O₁` and `O₂`, i.e. the spherical "line of centres". -/
theorem sphere_slerp_inter_eq_singleton {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ d : ℝ}
    (hd : sdist O₁ O₂ = d) (hdpos : 0 < d) (hdpi : d < Real.pi)
    (hangle : Real.cos ρ₂ = Real.cos ρ₁ * Real.cos d + Real.sin ρ₁ * Real.sin d) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) := by
  set c : ℝ := Real.cos d with hc_def
  set s : ℝ := Real.sin d with hs_def
  have hO₁O₁ : (⟪O₁, O₁⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, h₁]; norm_num
  have hO₂O₂ : (⟪O₂, O₂⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, h₂]; norm_num
  have hcio : (⟪O₁, O₂⟫ : ℝ) = c := by
    have h := cos_sdist O₁ O₂ h₁ h₂
    rw [hd] at h; rw [hc_def]; exact h.symm
  have hc21 : (⟪O₂, O₁⟫ : ℝ) = c := by rw [real_inner_comm]; exact hcio
  have hspos : 0 < s := Real.sin_pos_of_pos_of_lt_pi hdpos hdpi
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hs2 : s ^ 2 = 1 - c ^ 2 := by
    have h := Real.sin_sq_add_cos_sq d; rw [← hc_def, ← hs_def] at h; linarith
  -- the slerp point and the tangent vector W = O₂ - c • O₁
  set P : E := Real.cos ρ₁ • O₁ + (Real.sin ρ₁ / s) • (O₂ - c • O₁) with hP_def
  have hW1 : (⟪O₁, O₂ - c • O₁⟫ : ℝ) = 0 := by
    rw [inner_sub_right, real_inner_smul_right, hcio, hO₁O₁]; ring
  have hW1' : (⟪O₂ - c • O₁, O₁⟫ : ℝ) = 0 := by rw [real_inner_comm]; exact hW1
  have hWW : (⟪O₂ - c • O₁, O₂ - c • O₁⟫ : ℝ) = s ^ 2 := by
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
      hcio, hc21, hO₁O₁, hO₂O₂]; rw [hs2]; ring
  -- P is a unit vector lying on both circles (existence half, reused as the singleton witness)
  have hPP : (⟪P, P⟫ : ℝ) = 1 := by
    have e : (⟪P, P⟫ : ℝ)
        = Real.cos ρ₁ ^ 2 * ⟪O₁, O₁⟫
          + 2 * (Real.cos ρ₁ * (Real.sin ρ₁ / s)) * ⟪O₁, O₂ - c • O₁⟫
          + (Real.sin ρ₁ / s) ^ 2 * ⟪O₂ - c • O₁, O₂ - c • O₁⟫ := by
      rw [hP_def]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        real_inner_comm (O₂ - c • O₁) O₁]; ring
    rw [e, hO₁O₁, hW1, hWW]
    have hss : (Real.sin ρ₁ / s) ^ 2 * s ^ 2 = Real.sin ρ₁ ^ 2 := by field_simp
    linear_combination hss + Real.sin_sq_add_cos_sq ρ₁
  have hP_sphere : OnSphere P := by
    have hsq : ‖P‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq]; exact hPP
    have hfac : (‖P‖ - 1) * (‖P‖ + 1) = 0 := by nlinarith [hsq]
    rcases mul_eq_zero.mp hfac with h | h
    · show ‖P‖ = 1; linarith
    · exact absurd h (by have := norm_nonneg P; positivity)
  have hPO₁ : scos P O₁ = Real.cos ρ₁ := by
    rw [scos, hP_def, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hO₁O₁, hW1']; ring
  have hPO₂ : scos P O₂ = Real.cos ρ₂ := by
    have hsimp : Real.sin ρ₁ / s * s ^ 2 = Real.sin ρ₁ * s := by field_simp
    rw [scos, hP_def, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      inner_sub_left, real_inner_smul_left, hcio, hO₂O₂,
      show (1 : ℝ) - c * c = s ^ 2 from by linear_combination -hs2, hsimp]
    linear_combination -hangle
  -- the slerp point lies on the geodesic through the two centres (the spherical "line of
  -- centres"): it is a linear combination of `O₁` and `O₂`
  have hspan : P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) := by
    have hO1 : O₁ ∈ Submodule.span ℝ ({O₁, O₂} : Set E) := Submodule.subset_span (by simp)
    have hO2 : O₂ ∈ Submodule.span ℝ ({O₁, O₂} : Set E) := Submodule.subset_span (by simp)
    rw [hP_def]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hO1)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ hO2 (Submodule.smul_mem _ _ hO1)))
  refine ⟨P, Set.eq_singleton_iff_unique_mem.mpr ⟨⟨⟨hP_sphere, hPO₁⟩, ⟨hP_sphere, hPO₂⟩⟩, ?_⟩, hspan⟩
  -- uniqueness: any common point Q coincides with P
  rintro Q ⟨⟨hQsph, hQO₁⟩, ⟨-, hQO₂⟩⟩
  have hQQ : (⟪Q, Q⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hQsph]; norm_num
  have hQ1 : (⟪Q, O₁⟫ : ℝ) = Real.cos ρ₁ := by simpa [scos] using hQO₁
  have hQ2 : (⟪Q, O₂⟫ : ℝ) = Real.cos ρ₂ := by simpa [scos] using hQO₂
  have hQP : (⟪Q, P⟫ : ℝ) = 1 := by
    rw [hP_def, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      inner_sub_right, real_inner_smul_right, hQ1, hQ2]
    have hkey : Real.cos ρ₂ - c * Real.cos ρ₁ = Real.sin ρ₁ * s := by rw [hangle]; ring
    rw [hkey]
    have hss : Real.sin ρ₁ / s * (Real.sin ρ₁ * s) = Real.sin ρ₁ ^ 2 := by field_simp
    rw [hss]
    linear_combination Real.sin_sq_add_cos_sq ρ₁
  have hzero : (⟪Q - P, Q - P⟫ : ℝ) = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hQQ, hQP, hPP,
      real_inner_comm Q P, hQP]; ring
  have hQPeq : Q - P = 0 := by rwa [inner_self_eq_zero] at hzero
  exact sub_eq_zero.mp hQPeq

/-- **Uniqueness of the tangent point (external case).**  Two externally tangent spherical
circles meet in *exactly one* point, and that point lies on the geodesic joining the centres
(the spherical "line of centres") — the strengthening of `externallyTangent_has_common_point`
that justifies calling them tangent. -/
theorem externallyTangent_unique_common_point {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : ExternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hpos : 0 < ρ₁ + ρ₂) (hlt : ρ₁ + ρ₂ < Real.pi) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) :=
  sphere_slerp_inter_eq_singleton h₁ h₂ htan hpos hlt
    (by rw [← Real.cos_sub, show ρ₁ - (ρ₁ + ρ₂) = -ρ₂ from by ring, Real.cos_neg])

/-- **Uniqueness of the tangent point (internal case).**  Two internally tangent spherical
circles meet in *exactly one* point, lying on the geodesic joining the centres. -/
theorem internallyTangent_unique_common_point {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : InternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hpos : 0 < ρ₁ - ρ₂) (hlt : ρ₁ - ρ₂ < Real.pi) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) := by
  have hd : sdist O₁ O₂ = ρ₁ - ρ₂ := by rw [htan]; exact abs_of_pos hpos
  exact sphere_slerp_inter_eq_singleton h₁ h₂ hd hpos hlt
    (by rw [← Real.cos_sub]; congr 1; ring)

/-! ## Full characterization of the tangent point

Bundling the three facts proved above — the intersection is a singleton, the point of
contact lies on the geodesic through the centres, and it sits at the prescribed angular
radii from each centre — gives a complete description of the tangent point.  The radii
follow from `Real.arccos_cos`: a common point `P` has `scos P Oᵢ = cos ρᵢ`, and on the
admissible range `ρᵢ ∈ [0, π]` this inverts to `sdist P Oᵢ = ρᵢ`. -/

/-- **Tangent point — full specification (core).**  Under the hypotheses of
`sphere_slerp_inter_eq_singleton` together with `ρ₁, ρ₂ ∈ [0, π]`, the unique common point
`P` of the two circles (i) is the whole intersection, (ii) lies on the geodesic through the
centres `O₁, O₂`, and (iii) sits at spherical distance exactly `ρ₁` from `O₁` and `ρ₂` from
`O₂`.  This is the spherical analogue of "the point of contact lies on the line of centres,
at the two radii from the respective centres". -/
theorem sphere_slerp_tangent_point_spec {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ d : ℝ}
    (hd : sdist O₁ O₂ = d) (hdpos : 0 < d) (hdpi : d < Real.pi)
    (hangle : Real.cos ρ₂ = Real.cos ρ₁ * Real.cos d + Real.sin ρ₁ * Real.sin d)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁pi : ρ₁ ≤ Real.pi) (hρ₂0 : 0 ≤ ρ₂) (hρ₂pi : ρ₂ ≤ Real.pi) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) ∧
      sdist P O₁ = ρ₁ ∧ sdist P O₂ = ρ₂ := by
  obtain ⟨P, hsing, hspan⟩ :=
    sphere_slerp_inter_eq_singleton h₁ h₂ hd hdpos hdpi hangle
  -- the witness is itself a member of the intersection, so it lies on both circles
  have hPmem : P ∈ sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ := by rw [hsing]; rfl
  obtain ⟨⟨-, hsc1⟩, ⟨-, hsc2⟩⟩ := hPmem
  refine ⟨P, hsing, hspan, ?_, ?_⟩
  · -- sdist P O₁ = arccos (scos P O₁) = arccos (cos ρ₁) = ρ₁
    rw [sdist, show (⟪P, O₁⟫ : ℝ) = Real.cos ρ₁ from hsc1, Real.arccos_cos hρ₁0 hρ₁pi]
  · rw [sdist, show (⟪P, O₂⟫ : ℝ) = Real.cos ρ₂ from hsc2, Real.arccos_cos hρ₂0 hρ₂pi]

/-- **Tangent point — full specification (external case).**  For two externally tangent
spherical circles with `0 ≤ ρ₁`, `0 ≤ ρ₂`, `0 < ρ₁ + ρ₂` and `ρ₁ + ρ₂ < π`, the unique point
of contact lies on the geodesic through the centres and is at spherical distance `ρ₁` from
`O₁` and `ρ₂` from `O₂`.  (The two upper-range bounds `ρᵢ ≤ π` are automatic from
`ρ₁ + ρ₂ < π` and nonnegativity.) -/
theorem externallyTangent_tangent_point_spec {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : ExternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₂0 : 0 ≤ ρ₂) (hpos : 0 < ρ₁ + ρ₂) (hlt : ρ₁ + ρ₂ < Real.pi) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) ∧
      sdist P O₁ = ρ₁ ∧ sdist P O₂ = ρ₂ :=
  sphere_slerp_tangent_point_spec h₁ h₂ htan hpos hlt
    (by rw [← Real.cos_sub, show ρ₁ - (ρ₁ + ρ₂) = -ρ₂ from by ring, Real.cos_neg])
    hρ₁0 (by linarith) hρ₂0 (by linarith)

/-- **Tangent point — full specification (internal case).**  For two internally tangent
spherical circles with `0 ≤ ρ₂ < ρ₁ ≤ π` (the larger circle, radius `ρ₁`, containing the
smaller) and `ρ₁ - ρ₂ < π`, the unique point of contact lies on the geodesic through the
centres and is at spherical distance `ρ₁` from `O₁` and `ρ₂` from `O₂`.  The internal
analogue of `externallyTangent_tangent_point_spec`: it bundles
`internallyTangent_has_common_point` and `internallyTangent_unique_common_point` with the
radius read-off, using `d = ρ₁ - ρ₂` and the spherical law of cosines collapse
`cos ρ₁ · cos(ρ₁-ρ₂) + sin ρ₁ · sin(ρ₁-ρ₂) = cos ρ₂`. -/
theorem internallyTangent_tangent_point_spec {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : InternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hρ₂0 : 0 ≤ ρ₂) (hpos : 0 < ρ₁ - ρ₂) (hlt : ρ₁ - ρ₂ < Real.pi)
    (hρ₁pi : ρ₁ ≤ Real.pi) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) ∧
      sdist P O₁ = ρ₁ ∧ sdist P O₂ = ρ₂ := by
  have hd : sdist O₁ O₂ = ρ₁ - ρ₂ := by rw [htan]; exact abs_of_pos hpos
  exact sphere_slerp_tangent_point_spec h₁ h₂ hd hpos hlt
    (by rw [← Real.cos_sub, show ρ₁ - (ρ₁ - ρ₂) = ρ₂ from by ring])
    (by linarith) hρ₁pi hρ₂0 (by linarith)

end FeuerbachsTheoremOQ04
