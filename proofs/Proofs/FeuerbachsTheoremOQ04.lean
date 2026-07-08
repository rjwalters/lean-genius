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

/-! ## Inner-product form of the tangency criteria

Tangency is defined as a *distance* equation (`sdist = ρ₁ + ρ₂` externally,
`= |ρ₁ − ρ₂|` internally), but the quantity one actually computes from ambient
coordinates is the inner product `scos O₁ O₂ = ⟪O₁, O₂⟫`.  Since
`cos ∘ sdist = scos` (`cos_sdist`) and `cos` is injective on `[0, π]`, the
distance equations are equivalent to the single inner-product equations

  external:  `⟪O₁, O₂⟫ = cos (ρ₁ + ρ₂)`,   internal:  `⟪O₁, O₂⟫ = cos (ρ₁ − ρ₂)`,

valid whenever the relevant radius combination lies in `[0, π]` (so that it is a
legal spherical distance).  This is the bridge a coordinate-level Feuerbach
tangency proof needs: reduce "the nine-point circle is tangent to the incircle"
to one inner-product identity between their centres. -/

/-- **External tangency ⇔ inner-product equation.**  For model centres `O₁, O₂`,
external tangency `sdist O₁ O₂ = ρ₁ + ρ₂` is equivalent to
`scos O₁ O₂ = cos (ρ₁ + ρ₂)`, provided `ρ₁ + ρ₂ ∈ [0, π]`.  Forward: apply `cos`
and use `cos_sdist`.  Backward: `cos` is injective on `[0, π]`, and both
`sdist O₁ O₂` and `ρ₁ + ρ₂` lie there. -/
theorem externallyTangent_iff_scos {O₁ O₂ : E} (h₁ : OnSphere O₁) (h₂ : OnSphere O₂)
    {ρ₁ ρ₂ : ℝ} (hlo : 0 ≤ ρ₁ + ρ₂) (hhi : ρ₁ + ρ₂ ≤ Real.pi) :
    ExternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ scos O₁ O₂ = Real.cos (ρ₁ + ρ₂) := by
  unfold ExternallyTangent
  rw [← cos_sdist O₁ O₂ h₁ h₂]
  constructor
  · intro h; rw [h]
  · intro h
    exact Real.injOn_cos (Set.mem_Icc.mpr ⟨sdist_nonneg O₁ O₂, sdist_le_pi O₁ O₂⟩)
      (Set.mem_Icc.mpr ⟨hlo, hhi⟩) h

/-- **Internal tangency ⇔ inner-product equation.**  For model centres `O₁, O₂`,
internal tangency `sdist O₁ O₂ = |ρ₁ − ρ₂|` is equivalent to
`scos O₁ O₂ = cos (ρ₁ − ρ₂)` (using `cos |ρ₁ − ρ₂| = cos (ρ₁ − ρ₂)`), provided
`|ρ₁ − ρ₂| ≤ π`. -/
theorem internallyTangent_iff_scos {O₁ O₂ : E} (h₁ : OnSphere O₁) (h₂ : OnSphere O₂)
    {ρ₁ ρ₂ : ℝ} (hhi : |ρ₁ - ρ₂| ≤ Real.pi) :
    InternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ scos O₁ O₂ = Real.cos (ρ₁ - ρ₂) := by
  unfold InternallyTangent
  rw [← cos_sdist O₁ O₂ h₁ h₂, ← Real.cos_abs (ρ₁ - ρ₂)]
  constructor
  · intro h; rw [h]
  · intro h
    exact Real.injOn_cos (Set.mem_Icc.mpr ⟨sdist_nonneg O₁ O₂, sdist_le_pi O₁ O₂⟩)
      (Set.mem_Icc.mpr ⟨abs_nonneg _, hhi⟩) h

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
spherical circles with `0 ≤ ρ₂`, `ρ₁ ≤ π`, `0 < ρ₁ − ρ₂` and `ρ₁ − ρ₂ < π`, the unique point
of contact lies on the geodesic through the centres and is at spherical distance `ρ₁` from
`O₁` and `ρ₂` from `O₂` — the internal analogue of `externallyTangent_tangent_point_spec`.
Internal tangency puts the centres at spherical distance `ρ₁ − ρ₂` (the smaller circle sits
inside the larger, touching from within), and the addition law degenerates to
`cos ρ₂ = cos ρ₁ cos(ρ₁−ρ₂) + sin ρ₁ sin(ρ₁−ρ₂)` since `ρ₁ − (ρ₁−ρ₂) = ρ₂`.  The remaining
range bounds `0 ≤ ρ₁` and `ρ₂ ≤ π` are automatic from `0 < ρ₁ − ρ₂` and `ρ₁ ≤ π`. -/
theorem internallyTangent_tangent_point_spec {O₁ O₂ : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : InternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hρ₂0 : 0 ≤ ρ₂) (hρ₁pi : ρ₁ ≤ Real.pi) (hpos : 0 < ρ₁ - ρ₂) (hlt : ρ₁ - ρ₂ < Real.pi) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      P ∈ Submodule.span ℝ ({O₁, O₂} : Set E) ∧
      sdist P O₁ = ρ₁ ∧ sdist P O₂ = ρ₂ := by
  have hd : sdist O₁ O₂ = ρ₁ - ρ₂ := by rw [htan]; exact abs_of_pos hpos
  exact sphere_slerp_tangent_point_spec h₁ h₂ hd hpos hlt
    (by rw [← Real.cos_sub, show ρ₁ - (ρ₁ - ρ₂) = ρ₂ from by ring])
    (by linarith) hρ₁pi hρ₂0 (by linarith)

/-! ## The common tangent geodesic at the point of contact

The point of contact `P` of two tangent circles carries a **common tangent geodesic**, and
that geodesic is perpendicular to the geodesic through the two centres (the "line of
centres").  This is the last elementary metric fact underneath a spherical Feuerbach
argument, and the spherical form of the Euclidean statement "two tangent circles share a
common tangent line at the contact point, perpendicular to the line joining the centres".

In the sphere model the tangent space at a model point `P` is the orthogonal complement
`{P}ᗮ`; the geodesic from `P` towards a centre `O` leaves `P` in the **radial direction**
`radialDir P O = O − ⟪O,P⟫ • P` (the component of `O` orthogonal to `P`); and a tangent-space
vector `T` (one with `⟪T,P⟫ = 0`) is tangent to the circle centred at `O` exactly when it is
perpendicular to that radial direction — equivalently, since `⟪T,P⟫ = 0`, when `⟪T,O⟫ = 0`
(`isTangentDir_iff`).

Because the contact point lies on the geodesic through the centres (`P ∈ span{O₁,O₂}`, the
`hspan` conjunct proved above), any direction `T` orthogonal to *both* centres is
automatically (i) in the tangent space at `P`, (ii) tangent to *both* circles — a common
tangent — and (iii) orthogonal to the whole centre-plane `span{O₁,O₂}`, hence to both radial
directions `radialDir P O₁`, `radialDir P O₂` (which lie in that plane by
`radialDir_mem_span`): the common tangent is perpendicular to the line of centres
(`common_perp_tangent`).  A nonzero such `T` exists as soon as the ambient dimension exceeds
`2` (`exists_common_perp_tangent`), so the statement is not vacuous — on a genuine sphere
`Sⁿ`, `n ≥ 2`, the common tangent geodesic is real. -/

/-- The **radial direction** at a model point `P` towards a centre `O`: the component of `O`
orthogonal to `P`.  It spans the tangent line at `P` of the geodesic from `P` to `O` (the
"spherical radius" direction). -/
noncomputable def radialDir (P O : E) : E := O - (⟪O, P⟫ : ℝ) • P

/-- The inner product of an arbitrary vector with a radial direction. -/
theorem inner_radialDir (T P O : E) :
    (⟪T, radialDir P O⟫ : ℝ) = ⟪T, O⟫ - ⟪O, P⟫ * ⟪T, P⟫ := by
  rw [radialDir, inner_sub_right, real_inner_smul_right]

/-- On the tangent space at `P` (vectors `T` with `⟪T,P⟫ = 0`) the radial inner product
collapses to the inner product with the centre itself. -/
theorem inner_radialDir_of_tangent {T P O : E} (hTP : (⟪T, P⟫ : ℝ) = 0) :
    (⟪T, radialDir P O⟫ : ℝ) = ⟪T, O⟫ := by
  rw [inner_radialDir, hTP]; ring

/-- A radial direction at `P` towards a centre `O` lies in the plane `span{O₁,O₂}` spanned by
the two centres whenever both `P` and `O` do — so the radii sit on the geodesic through the
centres. -/
theorem radialDir_mem_span {O₁ O₂ P O : E}
    (hP : P ∈ Submodule.span ℝ ({O₁, O₂} : Set E))
    (hO : O ∈ Submodule.span ℝ ({O₁, O₂} : Set E)) :
    radialDir P O ∈ Submodule.span ℝ ({O₁, O₂} : Set E) :=
  Submodule.sub_mem _ hO (Submodule.smul_mem _ _ hP)

/-- A direction `T` is **tangent** to the spherical circle centred at `O` at the model point
`P` when it lies in the tangent space at `P` (`⟪T,P⟫ = 0`) and is perpendicular to the radial
direction towards `O`. -/
def IsTangentDir (T P O : E) : Prop :=
  (⟪T, P⟫ : ℝ) = 0 ∧ (⟪T, radialDir P O⟫ : ℝ) = 0

/-- **Tangent ⇔ perpendicular to the centre.**  A tangent-space vector at `P` is tangent to
the circle centred at `O` exactly when it is orthogonal to the centre `O` itself. -/
theorem isTangentDir_iff {T P O : E} :
    IsTangentDir T P O ↔ (⟪T, P⟫ : ℝ) = 0 ∧ (⟪T, O⟫ : ℝ) = 0 := by
  unfold IsTangentDir
  constructor
  · rintro ⟨hTP, hr⟩; exact ⟨hTP, by rwa [inner_radialDir_of_tangent hTP] at hr⟩
  · rintro ⟨hTP, hO⟩; exact ⟨hTP, by rw [inner_radialDir_of_tangent hTP, hO]⟩

/-- A vector orthogonal to both centres `O₁, O₂` is orthogonal to every vector of the plane
`span{O₁,O₂}` they span — the plane carrying the line-of-centres geodesic. -/
theorem inner_eq_zero_of_mem_span_pair {T O₁ O₂ : E}
    (h₁ : (⟪T, O₁⟫ : ℝ) = 0) (h₂ : (⟪T, O₂⟫ : ℝ) = 0)
    {x : E} (hx : x ∈ Submodule.span ℝ ({O₁, O₂} : Set E)) :
    (⟪T, x⟫ : ℝ) = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h₁, h₂]; ring

/-- **Common perpendicular tangent at the point of contact (dimension-free core).**  Let `P`
lie on the geodesic through the two centres (`P ∈ span{O₁,O₂}` — the `hspan` conjunct proved
for the contact point of any pair of tangent circles).  Any direction `T` orthogonal to both
centres is then (i) in the tangent space at `P` (`⟪T,P⟫ = 0`), (ii) a **common tangent** to
the circles centred at `O₁` and `O₂` at `P`, and (iii) orthogonal to the entire centre-plane
`span{O₁,O₂}` — in particular to both radial directions `radialDir P O₁`, `radialDir P O₂`.
So a common tangent at the contact point is perpendicular to the line of centres. -/
theorem common_perp_tangent {O₁ O₂ P T : E}
    (hP : P ∈ Submodule.span ℝ ({O₁, O₂} : Set E))
    (hTO₁ : (⟪T, O₁⟫ : ℝ) = 0) (hTO₂ : (⟪T, O₂⟫ : ℝ) = 0) :
    (⟪T, P⟫ : ℝ) = 0 ∧ IsTangentDir T P O₁ ∧ IsTangentDir T P O₂ ∧
      ∀ x ∈ Submodule.span ℝ ({O₁, O₂} : Set E), (⟪T, x⟫ : ℝ) = 0 := by
  have hTP : (⟪T, P⟫ : ℝ) = 0 := inner_eq_zero_of_mem_span_pair hTO₁ hTO₂ hP
  refine ⟨hTP, isTangentDir_iff.mpr ⟨hTP, hTO₁⟩, isTangentDir_iff.mpr ⟨hTP, hTO₂⟩, ?_⟩
  intro x hx
  exact inner_eq_zero_of_mem_span_pair hTO₁ hTO₂ hx

/-- **Existence of a common perpendicular tangent (non-vacuity).**  Once the ambient
dimension exceeds `2`, there is a *nonzero* direction orthogonal to both centres, so the
common tangent of `common_perp_tangent` is a genuine geodesic — on a real sphere `Sⁿ` with
`n ≥ 2` (`finrank ℝ E ≥ 3`) the contact point has an honest common tangent line.  Proof: the
centre-plane `span{O₁,O₂}` has dimension `≤ 2`, so its orthogonal complement has positive
dimension and hence a nonzero vector, which is orthogonal to every element of the plane. -/
theorem exists_common_perp_tangent [FiniteDimensional ℝ E] (O₁ O₂ : E)
    (hdim : 2 < Module.finrank ℝ E) :
    ∃ T : E, T ≠ 0 ∧ (⟪T, O₁⟫ : ℝ) = 0 ∧ (⟪T, O₂⟫ : ℝ) = 0 := by
  classical
  set K : Submodule ℝ E := Submodule.span ℝ ({O₁, O₂} : Set E) with hK
  -- the centre-plane has dimension at most 2
  have hKle : Module.finrank ℝ K ≤ 2 := by
    have h := finrank_span_le_card (R := ℝ) ({O₁, O₂} : Set E)
    rw [← hK] at h
    refine h.trans ?_
    have hsub : ({O₁, O₂} : Set E).toFinset ⊆ ({O₁, O₂} : Finset E) := by
      intro x; simp
    exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
  -- so its orthogonal complement has positive dimension, hence a nonzero vector
  have hsum : Module.finrank ℝ K + Module.finrank ℝ Kᗮ = Module.finrank ℝ E :=
    K.finrank_add_finrank_orthogonal
  have hpos : 0 < Module.finrank ℝ Kᗮ := by omega
  haveI hnt : Nontrivial Kᗮ := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨w, hw₀⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
  have hwne : (w : E) ≠ 0 := fun h => hw₀ (Submodule.coe_eq_zero.mp h)
  have hO₁ : O₁ ∈ K := Submodule.subset_span (by simp)
  have hO₂ : O₂ ∈ K := Submodule.subset_span (by simp)
  refine ⟨(w : E), hwne, ?_, ?_⟩
  · rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal hO₁ w.2
  · rw [real_inner_comm]; exact Submodule.inner_right_of_mem_orthogonal hO₂ w.2

/-- **The two tangent circles share a common perpendicular tangent at their contact point
(external case).**  For two externally tangent spherical circles, any direction `T`
orthogonal to both centres is a common tangent — tangent to *both* circles — at the unique
point of contact, and is perpendicular to the entire line-of-centres plane.  (Such a nonzero
`T` exists whenever `finrank ℝ E > 2`, by `exists_common_perp_tangent`.) -/
theorem externallyTangent_common_perp_tangent {O₁ O₂ T : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : ExternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₂0 : 0 ≤ ρ₂) (hpos : 0 < ρ₁ + ρ₂) (hlt : ρ₁ + ρ₂ < Real.pi)
    (hTO₁ : (⟪T, O₁⟫ : ℝ) = 0) (hTO₂ : (⟪T, O₂⟫ : ℝ) = 0) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      IsTangentDir T P O₁ ∧ IsTangentDir T P O₂ ∧
      ∀ x ∈ Submodule.span ℝ ({O₁, O₂} : Set E), (⟪T, x⟫ : ℝ) = 0 := by
  obtain ⟨P, hsing, hspan, -, -⟩ :=
    externallyTangent_tangent_point_spec h₁ h₂ htan hρ₁0 hρ₂0 hpos hlt
  obtain ⟨-, ht1, ht2, hperp⟩ := common_perp_tangent hspan hTO₁ hTO₂
  exact ⟨P, hsing, ht1, ht2, hperp⟩

/-- **The two tangent circles share a common perpendicular tangent at their contact point
(internal case).**  The internal analogue of `externallyTangent_common_perp_tangent`. -/
theorem internallyTangent_common_perp_tangent {O₁ O₂ T : E}
    (h₁ : OnSphere O₁) (h₂ : OnSphere O₂) {ρ₁ ρ₂ : ℝ}
    (htan : InternallyTangent O₁ ρ₁ O₂ ρ₂)
    (hρ₂0 : 0 ≤ ρ₂) (hρ₁pi : ρ₁ ≤ Real.pi) (hpos : 0 < ρ₁ - ρ₂) (hlt : ρ₁ - ρ₂ < Real.pi)
    (hTO₁ : (⟪T, O₁⟫ : ℝ) = 0) (hTO₂ : (⟪T, O₂⟫ : ℝ) = 0) :
    ∃ P : E, sCircle O₁ ρ₁ ∩ sCircle O₂ ρ₂ = {P} ∧
      IsTangentDir T P O₁ ∧ IsTangentDir T P O₂ ∧
      ∀ x ∈ Submodule.span ℝ ({O₁, O₂} : Set E), (⟪T, x⟫ : ℝ) = 0 := by
  obtain ⟨P, hsing, hspan, -, -⟩ :=
    internallyTangent_tangent_point_spec h₁ h₂ htan hρ₂0 hρ₁pi hpos hlt
  obtain ⟨-, ht1, ht2, hperp⟩ := common_perp_tangent hspan hTO₁ hTO₂
  exact ⟨P, hsing, ht1, ht2, hperp⟩

/-! ## Tangency of a spherical circle to a great circle

The incircle and excircles of a spherical triangle are characterised by tangency to the
triangle's *sides* — arcs of great circles — rather than to other circles.  A great circle
is the set of model points orthogonal to a fixed unit *pole* `N`; these are the "lines"
(geodesics) of spherical geometry.  This section records exactly when a spherical circle
`sCircle O ρ` is tangent to such a great circle and exhibits the contact point: the **foot
of the perpendicular** from the centre `O`, i.e. the orthogonal component `O − ⟪O,N⟫ • N`
renormalised to a unit vector.  The tangency criterion is the spherical analogue of
"distance from centre to line = radius": since the spherical distance from `O` to the
great circle is `arcsin |⟪O,N⟫|`, tangency is `|⟪O, N⟫| = sin ρ`.  This is the primitive a
spherical incircle construction consumes three times, once per side. -/

/-- The **great circle** with unit pole `N`: the model points orthogonal to `N`.  These are
the geodesics of the spherical model — in particular the sides of a spherical triangle. -/
def sGreatCircle (N : E) : Set E := {P | OnSphere P ∧ (⟪P, N⟫ : ℝ) = 0}

/-- The **foot of the perpendicular** from the centre `O` of a spherical circle of angular
radius `ρ` onto the great circle with pole `N`: the orthogonal component `O − ⟪O,N⟫ • N`
renormalised by `(cos ρ)⁻¹`.  When `sCircle O ρ` is tangent to the great circle this is
their unique common point (`circle_tangent_greatCircle_inter`). -/
noncomputable def greatCircleFoot (O N : E) (ρ : ℝ) : E :=
  (Real.cos ρ)⁻¹ • (O - (⟪O, N⟫ : ℝ) • N)

/-- A spherical circle `sCircle O ρ` is **tangent to the great circle** with pole `N` when
the spherical distance from the centre to the great circle equals the angular radius.  That
distance is `arcsin |⟪O, N⟫|`, so the algebraic criterion is `|⟪O, N⟫| = sin ρ` — the
spherical shadow of the Euclidean "distance from centre to the line equals the radius". -/
def TangentToGreatCircle (O : E) (ρ : ℝ) (N : E) : Prop :=
  |(⟪O, N⟫ : ℝ)| = Real.sin ρ

/-- The squared norm of the orthogonal component of a unit centre `O` off a unit pole `N`
is `1 − ⟪O,N⟫²` (the spherical Pythagoras for the projection onto the great circle). -/
theorem inner_orthoComp_self {O N : E} (hO : OnSphere O) (hN : OnSphere N) :
    (⟪O - (⟪O, N⟫ : ℝ) • N, O - (⟪O, N⟫ : ℝ) • N⟫ : ℝ) = 1 - (⟪O, N⟫ : ℝ) ^ 2 := by
  have hOO : (⟪O, O⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hO]; norm_num
  have hNN : (⟪N, N⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hN]; norm_num
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [hOO, hNN, real_inner_comm N O]
  ring

/-- The inner product of the orthogonal component of `O` off `N` with `O` itself is
`1 − ⟪O,N⟫²`. -/
theorem inner_orthoComp_left {O N : E} (hO : OnSphere O) :
    (⟪O - (⟪O, N⟫ : ℝ) • N, O⟫ : ℝ) = 1 - (⟪O, N⟫ : ℝ) ^ 2 := by
  have hOO : (⟪O, O⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hO]; norm_num
  simp only [inner_sub_left, real_inner_smul_left]
  rw [hOO, real_inner_comm N O]
  ring

/-- **The foot of the perpendicular is the contact point.**  If `sCircle O ρ` is tangent to
the great circle with pole `N` (with `0 ≤ ρ < π/2`, so the circle is a genuine small
circle), then `greatCircleFoot O N ρ` is a model point lying on *both* the circle and the
great circle.  This is the existence half of the incircle-to-side tangency primitive. -/
theorem greatCircleFoot_mem {O N : E} {ρ : ℝ}
    (hO : OnSphere O) (hN : OnSphere N) (hρ0 : 0 ≤ ρ) (hρ2 : ρ < Real.pi / 2)
    (htan : TangentToGreatCircle O ρ N) :
    OnSphere (greatCircleFoot O N ρ) ∧
      greatCircleFoot O N ρ ∈ sCircle O ρ ∧
      greatCircleFoot O N ρ ∈ sGreatCircle N := by
  have hcpos : 0 < Real.cos ρ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hρ2⟩
  have hcne : Real.cos ρ ≠ 0 := ne_of_gt hcpos
  -- the tangency criterion, squared
  have hsq : (⟪O, N⟫ : ℝ) ^ 2 = (Real.sin ρ) ^ 2 := by rw [← sq_abs, htan]
  -- the orthogonal component has squared norm cos²ρ
  have hperp : (⟪O - (⟪O, N⟫ : ℝ) • N, O - (⟪O, N⟫ : ℝ) • N⟫ : ℝ) = (Real.cos ρ) ^ 2 := by
    rw [inner_orthoComp_self hO hN, hsq]; linarith [Real.sin_sq_add_cos_sq ρ]
  -- foot has unit inner product with itself
  have hFF : (⟪greatCircleFoot O N ρ, greatCircleFoot O N ρ⟫ : ℝ) = 1 := by
    have e : (⟪greatCircleFoot O N ρ, greatCircleFoot O N ρ⟫ : ℝ)
        = (Real.cos ρ)⁻¹ * ((Real.cos ρ)⁻¹ * (Real.cos ρ) ^ 2) := by
      simp only [greatCircleFoot, real_inner_smul_left, real_inner_smul_right, hperp]
    rw [e]; field_simp
  -- foot is a model point
  have hFsphere : OnSphere (greatCircleFoot O N ρ) := by
    have hsqn : ‖greatCircleFoot O N ρ‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]; exact hFF
    have hfac : (‖greatCircleFoot O N ρ‖ - 1) * (‖greatCircleFoot O N ρ‖ + 1) = 0 := by
      nlinarith [hsqn]
    rcases mul_eq_zero.mp hfac with h | h
    · show ‖greatCircleFoot O N ρ‖ = 1; linarith
    · exact absurd h (by have := norm_nonneg (greatCircleFoot O N ρ); positivity)
  -- foot lies on the circle: scos = cos ρ
  have hFO : scos (greatCircleFoot O N ρ) O = Real.cos ρ := by
    have e : (⟪greatCircleFoot O N ρ, O⟫ : ℝ)
        = (Real.cos ρ)⁻¹ * (1 - (⟪O, N⟫ : ℝ) ^ 2) := by
      simp only [greatCircleFoot, real_inner_smul_left, inner_orthoComp_left hO]
    rw [scos, e, hsq, show (1 : ℝ) - (Real.sin ρ) ^ 2 = (Real.cos ρ) ^ 2 from by
      linarith [Real.sin_sq_add_cos_sq ρ]]
    field_simp
  -- foot lies on the great circle: ⟪·, N⟫ = 0
  have hFN : (⟪greatCircleFoot O N ρ, N⟫ : ℝ) = 0 := by
    have hNN : (⟪N, N⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hN]; norm_num
    simp only [greatCircleFoot, real_inner_smul_left, inner_sub_left, real_inner_smul_left, hNN]
    ring
  exact ⟨hFsphere, ⟨hFsphere, hFO⟩, hFsphere, hFN⟩

/-- **Tangent circles meet a side in exactly one point.**  If `sCircle O ρ` is tangent to
the great circle with pole `N` (with `0 ≤ ρ < π/2`), their intersection is the single
contact point `greatCircleFoot O N ρ`.  This upgrades the existence lemma to genuine
tangency (one common point, not two), and is the exact fact a spherical incircle
construction needs for each of the triangle's three sides. -/
theorem circle_tangent_greatCircle_inter {O N : E} {ρ : ℝ}
    (hO : OnSphere O) (hN : OnSphere N) (hρ0 : 0 ≤ ρ) (hρ2 : ρ < Real.pi / 2)
    (htan : TangentToGreatCircle O ρ N) :
    sCircle O ρ ∩ sGreatCircle N = {greatCircleFoot O N ρ} := by
  have hcpos : 0 < Real.cos ρ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hρ2⟩
  have hcne : Real.cos ρ ≠ 0 := ne_of_gt hcpos
  obtain ⟨hFsphere, hFcirc, hFgc⟩ := greatCircleFoot_mem hO hN hρ0 hρ2 htan
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hFcirc, hFgc⟩, ?_⟩
  rintro Q ⟨⟨hQsphere, hQO⟩, -, hQN⟩
  have hQO' : (⟪Q, O⟫ : ℝ) = Real.cos ρ := hQO
  have hQF : scos Q (greatCircleFoot O N ρ) = 1 := by
    have e : (⟪Q, greatCircleFoot O N ρ⟫ : ℝ)
        = (Real.cos ρ)⁻¹ * ((⟪Q, O⟫ : ℝ) - (⟪O, N⟫ : ℝ) * (⟪Q, N⟫ : ℝ)) := by
      simp only [greatCircleFoot, real_inner_smul_right, inner_sub_right, real_inner_smul_right]
    rw [scos, e, hQN, hQO', mul_zero, sub_zero]
    field_simp
  exact (scos_eq_one_iff hQsphere hFsphere).mp hQF

/-- The contact point is at spherical distance exactly `ρ` from the circle's centre — it
genuinely lies *on* the circle, the spherical restatement of the foot lemma via `sdist`. -/
theorem sdist_greatCircleFoot_center {O N : E} {ρ : ℝ}
    (hO : OnSphere O) (hN : OnSphere N) (hρ0 : 0 ≤ ρ) (hρ2 : ρ < Real.pi / 2)
    (htan : TangentToGreatCircle O ρ N) :
    sdist (greatCircleFoot O N ρ) O = ρ := by
  obtain ⟨hFsphere, hFcirc, -⟩ := greatCircleFoot_mem hO hN hρ0 hρ2 htan
  have hρπ : ρ ≤ Real.pi := by linarith [Real.pi_pos]
  exact ((mem_sCircle_iff_sdist hO hρ0 hρπ (greatCircleFoot O N ρ)).mp hFcirc).2

/-- **Great circles are the spherical circles of angular radius `π/2`.**  With unit pole
`N`, `sGreatCircle N = sCircle N (π/2)`, since `cos (π/2) = 0` and membership of both is
`⟪P, N⟫ = 0`.  This unifies the two tangency notions: tangency to a "side" is tangency to a
particular circle, so a spherical incircle is tangent (in the circle–circle sense of the
earlier sections) to three radius-`π/2` circles centred at the side poles. -/
theorem sGreatCircle_eq_sCircle (N : E) : sGreatCircle N = sCircle N (Real.pi / 2) := by
  simp only [sGreatCircle, sCircle, scos, Real.cos_pi_div_two]

/-! ## The spherical incircle of a spherical triangle

A spherical triangle is presented by the unit **poles** `Nₐ, N_b, N_c` of its three side
great circles.  A spherical **incircle** is a circle `sCircle O ρ` tangent to all three
sides.  The tangency primitive `circle_tangent_greatCircle_inter` then delivers, for free,
that such an incircle touches each side in exactly one point — the corresponding foot of the
perpendicular.  This is the spherical form of "the incircle is tangent to all three sides",
the first ingredient of a spherical Feuerbach configuration.  (Existence/uniqueness of the
incenter `O` for a given triangle is the remaining hard step and is not asserted here.) -/

/-- A circle `sCircle O ρ` is a **spherical incircle** for the triangle with side poles
`Nₐ, N_b, N_c` when it is tangent to all three sides. -/
def SphericalIncircle (Na Nb Nc O : E) (ρ : ℝ) : Prop :=
  TangentToGreatCircle O ρ Na ∧ TangentToGreatCircle O ρ Nb ∧ TangentToGreatCircle O ρ Nc

/-- **A spherical incircle meets each side in exactly one point.**  For an incircle
`sCircle O ρ` (with `0 ≤ ρ < π/2`) of the triangle with unit side poles `Nₐ, N_b, N_c`, the
intersection with each side great circle is the singleton foot of the perpendicular from the
centre `O`.  Three applications of `circle_tangent_greatCircle_inter`: the incircle is
tangent to all three sides, with explicit contact points. -/
theorem sphericalIncircle_contact_points {Na Nb Nc O : E} {ρ : ℝ}
    (hO : OnSphere O) (hNa : OnSphere Na) (hNb : OnSphere Nb) (hNc : OnSphere Nc)
    (hρ0 : 0 ≤ ρ) (hρ2 : ρ < Real.pi / 2)
    (hinc : SphericalIncircle Na Nb Nc O ρ) :
    sCircle O ρ ∩ sGreatCircle Na = {greatCircleFoot O Na ρ} ∧
      sCircle O ρ ∩ sGreatCircle Nb = {greatCircleFoot O Nb ρ} ∧
      sCircle O ρ ∩ sGreatCircle Nc = {greatCircleFoot O Nc ρ} :=
  ⟨circle_tangent_greatCircle_inter hO hNa hρ0 hρ2 hinc.1,
   circle_tangent_greatCircle_inter hO hNb hρ0 hρ2 hinc.2.1,
   circle_tangent_greatCircle_inter hO hNc hρ0 hρ2 hinc.2.2⟩

/-! ## Spherical angle bisectors — the equidistant-from-two-sides locus

Locating the **incenter** of a spherical triangle (the remaining hard step above) is a
matter of intersecting angle bisectors: the incenter is the point equidistant from all
three sides.  The material below characterises that equidistant locus.

The spherical distance from a point `O` to the side with unit pole `N` is `arcsin |⟪O, N⟫|`
(the criterion `TangentToGreatCircle` records the case where it equals `ρ`).  So `O` is
**equidistant** from the two sides with poles `Na, Nb` exactly when `|⟪O, Na⟫| = |⟪O, Nb⟫|`.
This locus splits, by the sign of the equality, into the two **angle bisectors** — the great
circles with poles `Na − Nb` (internal) and `Na + Nb` (external).  These two bisector poles
are orthogonal, so the internal and external bisectors are themselves perpendicular great
circles, exactly as in the Euclidean picture.  An incircle centre, being tangent to (hence
equidistant from) all three sides, must lie on a bisector of each of the three pairs — the
standard characterisation that pins the incenter as an intersection of bisectors. -/

/-- **The two angle bisectors are perpendicular.**  For unit side poles `Na, Nb`, the poles
`Na − Nb` and `Na + Nb` of the internal and external bisector great circles are orthogonal
(`‖Na‖² − ‖Nb‖² = 0`), so the two bisectors meet at right angles. -/
theorem bisector_poles_orthogonal {Na Nb : E} (hNa : OnSphere Na) (hNb : OnSphere Nb) :
    (⟪Na - Nb, Na + Nb⟫ : ℝ) = 0 := by
  have hNaNa : (⟪Na, Na⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hNa]; norm_num
  have hNbNb : (⟪Nb, Nb⟫ : ℝ) = 1 := by rw [real_inner_self_eq_norm_sq, hNb]; norm_num
  have hcomm : (⟪Nb, Na⟫ : ℝ) = ⟪Na, Nb⟫ := real_inner_comm Na Nb
  rw [inner_sub_left, inner_add_right, inner_add_right, hNaNa, hNbNb, hcomm]
  ring

/-- **The equidistant locus is the union of the two angle bisectors.**  A point `O` is at
equal spherical distance from the two sides with poles `Na, Nb` (equivalently `|⟪O, Na⟫| =
|⟪O, Nb⟫|`) iff it lies on the internal bisector `⟪O, Na − Nb⟫ = 0` or the external bisector
`⟪O, Na + Nb⟫ = 0`.  Pure sign-analysis of the absolute-value equality (`abs_eq_abs`). -/
theorem equidistant_two_sides_iff (Na Nb O : E) :
    |(⟪O, Na⟫ : ℝ)| = |⟪O, Nb⟫| ↔
      (⟪O, Na - Nb⟫ : ℝ) = 0 ∨ (⟪O, Na + Nb⟫ : ℝ) = 0 := by
  rw [inner_sub_right, inner_add_right, abs_eq_abs]
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (h | h)
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-- **The incenter lies on an angle bisector of every pair of sides.**  The centre `O` of a
spherical incircle is tangent to (hence equidistant from) all three sides `Na, Nb, Nc`, so
for each of the three pairs it lies on the internal *or* external bisector great circle.
This is the structural fact underlying incenter existence: the incenter is a common point of
the three angle bisectors. -/
theorem sphericalIncircle_center_on_bisectors {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ) :
    ((⟪O, Na - Nb⟫ : ℝ) = 0 ∨ (⟪O, Na + Nb⟫ : ℝ) = 0) ∧
      ((⟪O, Nb - Nc⟫ : ℝ) = 0 ∨ (⟪O, Nb + Nc⟫ : ℝ) = 0) ∧
      ((⟪O, Na - Nc⟫ : ℝ) = 0 ∨ (⟪O, Na + Nc⟫ : ℝ) = 0) := by
  obtain ⟨ta, tb, tc⟩ := hinc
  exact ⟨(equidistant_two_sides_iff Na Nb O).mp (ta.trans tb.symm),
    (equidistant_two_sides_iff Nb Nc O).mp (tb.trans tc.symm),
    (equidistant_two_sides_iff Na Nc O).mp (ta.trans tc.symm)⟩

/-! ## Intersecting the bisectors — existence of the spherical incenter

The characterisation above says an incircle centre lies on a bisector of each pair.  To
*produce* an incenter we run the argument in reverse: intersect two of the bisector great
circles and read off a point equidistant from all three sides.  The intersection step is
`greatCircles_inter`; feeding it the two *internal* bisector poles `Na − Nb` and `Nb − Nc`
gives a point `O` with `⟪O, Na⟫ = ⟪O, Nb⟫ = ⟪O, Nc⟫`, whence `arcsin` of that common value is
the incircle radius.  This is the existence half of the spherical incircle. -/

/-- **Two great circles intersect in an antipodal pair.**  On a sphere of dimension `≥ 2`
(`finrank ℝ E > 2`), the two great circles with poles `Na, Nb` meet: there is a unit point `P`
on both, distinct from its antipode `−P`, which also lies on both.  Reuses
`exists_common_perp_tangent` for a nonzero direction orthogonal to both poles, then normalises
it to the sphere.  This is the primitive that lets the angle bisectors be intersected. -/
theorem greatCircles_inter [FiniteDimensional ℝ E] (Na Nb : E)
    (hdim : 2 < Module.finrank ℝ E) :
    ∃ P : E, OnSphere P ∧ P ≠ -P ∧
      P ∈ sGreatCircle Na ∧ P ∈ sGreatCircle Nb ∧
      (-P) ∈ sGreatCircle Na ∧ (-P) ∈ sGreatCircle Nb := by
  obtain ⟨T, hT0, hTa, hTb⟩ := exists_common_perp_tangent Na Nb hdim
  have hTnorm : ‖T‖ ≠ 0 := norm_ne_zero_iff.mpr hT0
  set P : E := (‖T‖⁻¹ : ℝ) • T with hP
  have hPon : OnSphere P := by
    rw [OnSphere, hP, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hTnorm
  have hPa : (⟪P, Na⟫ : ℝ) = 0 := by rw [hP, real_inner_smul_left, hTa, mul_zero]
  have hPb : (⟪P, Nb⟫ : ℝ) = 0 := by rw [hP, real_inner_smul_left, hTb, mul_zero]
  have hPne0 : P ≠ 0 := by
    intro h; rw [OnSphere, h, norm_zero] at hPon; exact one_ne_zero hPon.symm
  have hPantiOn : OnSphere (-P) := by rw [OnSphere, norm_neg]; exact hPon
  refine ⟨P, hPon, ?_, ⟨hPon, hPa⟩, ⟨hPon, hPb⟩,
    ⟨hPantiOn, by rw [inner_neg_left, hPa, neg_zero]⟩,
    ⟨hPantiOn, by rw [inner_neg_left, hPb, neg_zero]⟩⟩
  intro h
  have hpp : P + P = 0 := by nth_rewrite 1 [h]; exact neg_add_cancel P
  have h2 : (2 : ℝ) • P = 0 := by rw [two_smul]; exact hpp
  rcases smul_eq_zero.mp h2 with h20 | hp0
  · norm_num at h20
  · exact hPne0 hp0

/-- **Existence of the spherical incenter.**  For any three unit side poles `Na, Nb, Nc` on a
sphere of dimension `≥ 2` (`finrank ℝ E > 2`), there is a centre `O` and radius `ρ` making
`SphericalIncircle Na Nb Nc O ρ` — an inscribed circle tangent to all three sides.  Construct
`O` by intersecting the two internal angle bisectors (poles `Na − Nb`, `Nb − Nc`) via
`greatCircles_inter`; this forces `⟪O, Na⟫ = ⟪O, Nb⟫ = ⟪O, Nc⟫`, and `ρ = arcsin` of that
common inner product realises the equal tangency distance to each side. -/
theorem sphericalIncircle_exists [FiniteDimensional ℝ E] (Na Nb Nc : E)
    (hNa : OnSphere Na) (hdim : 2 < Module.finrank ℝ E) :
    ∃ (O : E) (ρ : ℝ), SphericalIncircle Na Nb Nc O ρ := by
  obtain ⟨O, hOon, -, ⟨-, hab⟩, ⟨-, hbc⟩, -, -⟩ :=
    greatCircles_inter (Na - Nb) (Nb - Nc) hdim
  -- the intersection point has equal inner product against all three poles
  have hab' : (⟪O, Na⟫ : ℝ) = ⟪O, Nb⟫ := by
    have := hab; rw [inner_sub_right] at this; linarith
  have hbc' : (⟪O, Nb⟫ : ℝ) = ⟪O, Nc⟫ := by
    have := hbc; rw [inner_sub_right] at this; linarith
  -- the common value is bounded by 1 in absolute value (Cauchy–Schwarz on unit vectors)
  have hbound : |(⟪O, Na⟫ : ℝ)| ≤ 1 := by
    have h := abs_real_inner_le_norm O Na; rw [hOon, hNa, mul_one] at h; exact h
  refine ⟨O, Real.arcsin |⟪O, Na⟫|, ?_, ?_, ?_⟩
  · show |(⟪O, Na⟫ : ℝ)| = Real.sin (Real.arcsin |⟪O, Na⟫|)
    rw [Real.sin_arcsin (by linarith [abs_nonneg (⟪O, Na⟫ : ℝ)]) hbound]
  · show |(⟪O, Nb⟫ : ℝ)| = Real.sin (Real.arcsin |⟪O, Na⟫|)
    rw [Real.sin_arcsin (by linarith [abs_nonneg (⟪O, Na⟫ : ℝ)]) hbound, ← hab']
  · show |(⟪O, Nc⟫ : ℝ)| = Real.sin (Real.arcsin |⟪O, Na⟫|)
    rw [Real.sin_arcsin (by linarith [abs_nonneg (⟪O, Na⟫ : ℝ)]) hbound, ← hbc', ← hab']

/-! ## Spherical excircles — the other three tritangent circles

`sphericalIncircle_exists` produced *one* circle tangent to all three sides, from intersecting
the two **internal** bisectors (poles `Na − Nb`, `Nb − Nc`), giving a centre with
`⟪O,Na⟫ = ⟪O,Nb⟫ = ⟪O,Nc⟫` — the incircle.  Replacing an internal bisector by the matching
**external** one (pole `Na + Nb` in place of `Na − Nb`) flips the sign of the inner product
against one pole, producing a centre still equidistant from all three sides but on the far
side of one of them: an **excircle**.  There are three such choices, one per vertex, so a
spherical triangle carries the same four tritangent circles (incircle + three excircles) as
its Euclidean counterpart — exactly the four circles the spherical nine-point circle must be
tangent to in Feuerbach's theorem.  The tangency criterion `|⟪O,N⟫| = sin ρ` is
sign-insensitive, so all four share the definition `SphericalIncircle`; the returned sign
relations `⟪O,Nᵢ⟫ = ±⟪O,Nⱼ⟫` are what tell the four circles apart. -/

/-- **Tritangent circles from equal side-distances.**  If a unit centre `O` is equidistant
from the three side great circles in the strong sense `|⟪O,Na⟫| = |⟪O,Nb⟫| = |⟪O,Nc⟫|`, then
`sCircle O (arcsin |⟪O,Na⟫|)` is tangent to all three sides.  This packages the common tail of
the incircle and excircle existence proofs. -/
theorem sphericalIncircle_of_abs_eq {Na Nb Nc O : E}
    (hO : OnSphere O) (hNa : OnSphere Na)
    (hab : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nb⟫|) (hac : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nc⟫|) :
    SphericalIncircle Na Nb Nc O (Real.arcsin |⟪O, Na⟫|) := by
  have hbound : |(⟪O, Na⟫ : ℝ)| ≤ 1 := by
    have h := abs_real_inner_le_norm O Na; rw [hO, hNa, mul_one] at h; exact h
  have key : |(⟪O, Na⟫ : ℝ)| = Real.sin (Real.arcsin |⟪O, Na⟫|) :=
    (Real.sin_arcsin (by linarith [abs_nonneg (⟪O, Na⟫ : ℝ)]) hbound).symm
  refine ⟨?_, ?_, ?_⟩
  · show |(⟪O, Na⟫ : ℝ)| = Real.sin (Real.arcsin |⟪O, Na⟫|); exact key
  · show |(⟪O, Nb⟫ : ℝ)| = Real.sin (Real.arcsin |⟪O, Na⟫|); rw [← hab]; exact key
  · show |(⟪O, Nc⟫ : ℝ)| = Real.sin (Real.arcsin |⟪O, Na⟫|); rw [← hac]; exact key

/-- **Existence of the spherical excircle opposite the first vertex.**  Intersecting the
*external* bisector of the `(Na, Nb)` pair (pole `Na + Nb`) with the *internal* bisector of
`(Nb, Nc)` (pole `Nb − Nc`) yields a centre `O` with `⟪O,Na⟫ = −⟪O,Nb⟫ = −⟪O,Nc⟫`: a circle
tangent to all three sides but on the far side of the first, an excircle.  The returned sign
relations record which tritangent circle this is, distinguishing it from the incircle
(`⟪O,Na⟫ = ⟪O,Nb⟫ = ⟪O,Nc⟫`). -/
theorem sphericalExcircleA_exists [FiniteDimensional ℝ E] (Na Nb Nc : E)
    (hNa : OnSphere Na) (hdim : 2 < Module.finrank ℝ E) :
    ∃ (O : E) (ρ : ℝ), SphericalIncircle Na Nb Nc O ρ ∧
      (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫ ∧ (⟪O, Nb⟫ : ℝ) = ⟪O, Nc⟫ := by
  obtain ⟨O, hOon, -, ⟨-, hab⟩, ⟨-, hbc⟩, -, -⟩ :=
    greatCircles_inter (Na + Nb) (Nb - Nc) hdim
  have hab' : (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫ := by
    have := hab; rw [inner_add_right] at this; linarith
  have hbc' : (⟪O, Nb⟫ : ℝ) = ⟪O, Nc⟫ := by
    have := hbc; rw [inner_sub_right] at this; linarith
  have hAB : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nb⟫| := by rw [hab', abs_neg]
  have hAC : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nc⟫| := by rw [hab', abs_neg, hbc']
  exact ⟨O, _, sphericalIncircle_of_abs_eq hOon hNa hAB hAC, hab', hbc'⟩

/-- **Existence of the spherical excircle opposite the second vertex.**  Uses the external
bisector of `(Na, Nb)` (pole `Na + Nb`) and the internal bisector of `(Na, Nc)` (pole
`Na − Nc`), yielding `⟪O,Na⟫ = −⟪O,Nb⟫` and `⟪O,Na⟫ = ⟪O,Nc⟫`; the sign of the second pole is
the one flipped. -/
theorem sphericalExcircleB_exists [FiniteDimensional ℝ E] (Na Nb Nc : E)
    (hNa : OnSphere Na) (hdim : 2 < Module.finrank ℝ E) :
    ∃ (O : E) (ρ : ℝ), SphericalIncircle Na Nb Nc O ρ ∧
      (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫ ∧ (⟪O, Na⟫ : ℝ) = ⟪O, Nc⟫ := by
  obtain ⟨O, hOon, -, ⟨-, hab⟩, ⟨-, hac⟩, -, -⟩ :=
    greatCircles_inter (Na + Nb) (Na - Nc) hdim
  have hab' : (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫ := by
    have := hab; rw [inner_add_right] at this; linarith
  have hac' : (⟪O, Na⟫ : ℝ) = ⟪O, Nc⟫ := by
    have := hac; rw [inner_sub_right] at this; linarith
  have hAB : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nb⟫| := by rw [hab', abs_neg]
  have hAC : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nc⟫| := by rw [hac']
  exact ⟨O, _, sphericalIncircle_of_abs_eq hOon hNa hAB hAC, hab', hac'⟩

/-- **Existence of the spherical excircle opposite the third vertex.**  Uses the internal
bisector of `(Na, Nb)` (pole `Na − Nb`) and the external bisector of `(Nb, Nc)` (pole
`Nb + Nc`), yielding `⟪O,Na⟫ = ⟪O,Nb⟫` and `⟪O,Nb⟫ = −⟪O,Nc⟫`; the sign of the third pole is
the one flipped. -/
theorem sphericalExcircleC_exists [FiniteDimensional ℝ E] (Na Nb Nc : E)
    (hNa : OnSphere Na) (hdim : 2 < Module.finrank ℝ E) :
    ∃ (O : E) (ρ : ℝ), SphericalIncircle Na Nb Nc O ρ ∧
      (⟪O, Na⟫ : ℝ) = ⟪O, Nb⟫ ∧ (⟪O, Nb⟫ : ℝ) = -⟪O, Nc⟫ := by
  obtain ⟨O, hOon, -, ⟨-, hab⟩, ⟨-, hbc⟩, -, -⟩ :=
    greatCircles_inter (Na - Nb) (Nb + Nc) hdim
  have hab' : (⟪O, Na⟫ : ℝ) = ⟪O, Nb⟫ := by
    have := hab; rw [inner_sub_right] at this; linarith
  have hbc' : (⟪O, Nb⟫ : ℝ) = -⟪O, Nc⟫ := by
    have := hbc; rw [inner_add_right] at this; linarith
  have hAB : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nb⟫| := by rw [hab']
  have hAC : |(⟪O, Na⟫ : ℝ)| = |⟪O, Nc⟫| := by rw [hab', hbc', abs_neg]
  exact ⟨O, _, sphericalIncircle_of_abs_eq hOon hNa hAB hAC, hab', hbc'⟩

/-! ## The four tritangent circles are genuinely distinct

`sphericalIncircle_exists` and `sphericalExcircle{A,B,C}_exists` produce four tritangent
circles, all satisfying the same predicate `SphericalIncircle`, distinguished only by the
sign relations `⟪O,Nᵢ⟫ = ±⟪O,Nⱼ⟫` they return: the incircle has all three inner products
equal (same sign), while each excircle *flips* one relation.  Feuerbach's theorem asserts
the spherical nine-point circle is tangent to *all four* — which is only meaningful if the
four are genuinely distinct circles.  This section certifies exactly that: an equal-sign
relation `⟪O,X⟫ = ⟪O,Y⟫` and the flipped relation `⟪O,X⟫ = -⟪O,Y⟫` cannot hold at one
tangent centre unless its radius is degenerate (`sin ρ = 0`, i.e. the "circle" is a point on
a side).  So on a nondegenerate radius the incircle and each excircle carry incompatible
sign patterns, hence are different circles.  All 0-sorry, 0-axiom. -/

/-- **Core sign exclusivity.**  If a circle `SphericalIncircle`-tangent to the side with pole
`Y` (`|⟪O,Y⟫| = sin ρ`) has a centre satisfying both the equal-sign relation `⟪O,X⟫ = ⟪O,Y⟫`
and the flipped relation `⟪O,X⟫ = -⟪O,Y⟫`, then its radius is degenerate: `sin ρ = 0`.
Adding the two relations forces `⟪O,Y⟫ = 0`, and tangency then reads off `sin ρ = 0`. -/
theorem tangent_signs_opposite_imp_sin_zero {O X Y : E} {ρ : ℝ}
    (htan : |(⟪O, Y⟫ : ℝ)| = Real.sin ρ)
    (heq : (⟪O, X⟫ : ℝ) = ⟪O, Y⟫)
    (hopp : (⟪O, X⟫ : ℝ) = -⟪O, Y⟫) :
    Real.sin ρ = 0 := by
  have hz : (⟪O, Y⟫ : ℝ) = 0 := by linarith
  rw [hz, abs_zero] at htan
  exact htan.symm

/-- **Incircle vs. excircle A/B: the `a`–`b` sign patterns are exclusive.**  Both excircles A
and B flip the first relation to `⟪O,Na⟫ = -⟪O,Nb⟫`, whereas the incircle has `⟪O,Na⟫ =
⟪O,Nb⟫`.  A single tangent centre carrying both forces a degenerate radius `sin ρ = 0` (its
`b`-side tangency vanishes). -/
theorem incircle_excircleAB_signs_exclusive {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hIn : (⟪O, Na⟫ : ℝ) = ⟪O, Nb⟫)
    (hEx : (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫) :
    Real.sin ρ = 0 :=
  tangent_signs_opposite_imp_sin_zero hinc.2.1 hIn hEx

/-- **Incircle vs. excircle C: the `b`–`c` sign patterns are exclusive.**  Excircle C flips
the second relation to `⟪O,Nb⟫ = -⟪O,Nc⟫`, whereas the incircle has `⟪O,Nb⟫ = ⟪O,Nc⟫`.  A
single tangent centre carrying both forces a degenerate radius `sin ρ = 0` (its `c`-side
tangency vanishes). -/
theorem incircle_excircleC_signs_exclusive {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hIn : (⟪O, Nb⟫ : ℝ) = ⟪O, Nc⟫)
    (hEx : (⟪O, Nb⟫ : ℝ) = -⟪O, Nc⟫) :
    Real.sin ρ = 0 :=
  tangent_signs_opposite_imp_sin_zero hinc.2.2 hIn hEx

/-- **On a nondegenerate radius, the incircle and excircle A/B sign patterns are
incompatible.**  For a genuine tritangent circle (`0 < ρ < π`, so `sin ρ > 0`) no centre can
satisfy both the incircle relation `⟪O,Na⟫ = ⟪O,Nb⟫` and the excircle relation `⟪O,Na⟫ =
-⟪O,Nb⟫`.  This certifies the incircle and the first two excircles are genuinely distinct
circles — a prerequisite for the "tangent to all four" statement of spherical Feuerbach. -/
theorem incircle_excircleAB_distinct {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hρpos : 0 < ρ) (hρlt : ρ < Real.pi)
    (hIn : (⟪O, Na⟫ : ℝ) = ⟪O, Nb⟫)
    (hEx : (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫) :
    False := by
  have h0 : Real.sin ρ = 0 := incircle_excircleAB_signs_exclusive hinc hIn hEx
  have hpos : 0 < Real.sin ρ := Real.sin_pos_of_pos_of_lt_pi hρpos hρlt
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-! ### Completing the pairwise-distinctness matrix

`incircle_excircleAB_distinct` above handles the incircle against excircles A and B (both
flip the `a`–`b` relation). Feuerbach's "tangent to all four" presupposes that *all four*
tritangent circles are pairwise distinct, i.e. every one of the six pairs is genuinely
different. The remaining pairs — incircle vs. excircle C, and the three excircle–excircle
pairs — are certified here. Each reduces to one of three sign-exclusivity engines
(`a`–`b`, `b`–`c`, `a`–`c`), so on a nondegenerate radius (`0 < ρ < π`, `sin ρ > 0`) no
single tangent centre can carry both circles' returned sign relations.

Recall the sign patterns each existence theorem returns (writing `sᵢ = ⟪O, Nᵢ⟫`, so
`|sₐ| = |s_b| = |s_c| = sin ρ`):

* incircle  `sphericalIncircle_exists`  : `sₐ =  s_b`, `s_b =  s_c`   (all equal)
* excircle A `sphericalExcircleA_exists` : `sₐ = -s_b`, `s_b =  s_c`   (`a` flipped)
* excircle B `sphericalExcircleB_exists` : `sₐ = -s_b`, `sₐ =  s_c`   (`b` flipped)
* excircle C `sphericalExcircleC_exists` : `sₐ =  s_b`, `s_b = -s_c`   (`c` flipped)
-/

/-- **`a`–`c` sign exclusivity.**  Companion to `incircle_excircleAB_signs_exclusive`
(the `a`–`b` engine) and `incircle_excircleC_signs_exclusive` (the `b`–`c` engine): a
tangent centre carrying both the equal relation `⟪O,Na⟫ = ⟪O,Nc⟫` and the flipped relation
`⟪O,Na⟫ = -⟪O,Nc⟫` has degenerate radius `sin ρ = 0` (its `c`-side tangency vanishes). -/
theorem incircle_excircle_ac_signs_exclusive {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hIn : (⟪O, Na⟫ : ℝ) = ⟪O, Nc⟫)
    (hEx : (⟪O, Na⟫ : ℝ) = -⟪O, Nc⟫) :
    Real.sin ρ = 0 :=
  tangent_signs_opposite_imp_sin_zero hinc.2.2 hIn hEx

/-- **Incircle vs. excircle C are genuinely distinct.**  The incircle has `⟪O,Nb⟫ = ⟪O,Nc⟫`
while excircle C flips this to `⟪O,Nb⟫ = -⟪O,Nc⟫`.  On a nondegenerate radius no centre can
satisfy both, so the incircle and excircle C are different circles.  (The `b`–`c` analogue
of `incircle_excircleAB_distinct`.) -/
theorem incircle_excircleC_distinct {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hρpos : 0 < ρ) (hρlt : ρ < Real.pi)
    (hIn : (⟪O, Nb⟫ : ℝ) = ⟪O, Nc⟫)
    (hEx : (⟪O, Nb⟫ : ℝ) = -⟪O, Nc⟫) :
    False := by
  have h0 : Real.sin ρ = 0 := incircle_excircleC_signs_exclusive hinc hIn hEx
  have hpos : 0 < Real.sin ρ := Real.sin_pos_of_pos_of_lt_pi hρpos hρlt
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **Excircles A and B are genuinely distinct.**  Both flip the `a`–`b` relation, so they
must be told apart on the `b`–`c` relation: excircle A returns `⟪O,Nb⟫ = ⟪O,Nc⟫`, whereas
excircle B's pair `⟪O,Na⟫ = -⟪O,Nb⟫`, `⟪O,Na⟫ = ⟪O,Nc⟫` forces `⟪O,Nb⟫ = -⟪O,Nc⟫`.  On a
nondegenerate radius these are incompatible, so excircles A and B are different circles. -/
theorem excircleA_excircleB_distinct {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hρpos : 0 < ρ) (hρlt : ρ < Real.pi)
    (hA_bc : (⟪O, Nb⟫ : ℝ) = ⟪O, Nc⟫)
    (hB_ab : (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫)
    (hB_ac : (⟪O, Na⟫ : ℝ) = ⟪O, Nc⟫) :
    False := by
  have hB_bc : (⟪O, Nb⟫ : ℝ) = -⟪O, Nc⟫ := by linarith
  have h0 : Real.sin ρ = 0 := incircle_excircleC_signs_exclusive hinc hA_bc hB_bc
  have hpos : 0 < Real.sin ρ := Real.sin_pos_of_pos_of_lt_pi hρpos hρlt
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **Excircles A and C are genuinely distinct.**  Excircle A flips the `a`–`b` relation
(`⟪O,Na⟫ = -⟪O,Nb⟫`) while excircle C keeps it equal (`⟪O,Na⟫ = ⟪O,Nb⟫`).  On a nondegenerate
radius these are incompatible, so excircles A and C are different circles. -/
theorem excircleA_excircleC_distinct {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hρpos : 0 < ρ) (hρlt : ρ < Real.pi)
    (hC_ab : (⟪O, Na⟫ : ℝ) = ⟪O, Nb⟫)
    (hA_ab : (⟪O, Na⟫ : ℝ) = -⟪O, Nb⟫) :
    False := by
  have h0 : Real.sin ρ = 0 := incircle_excircleAB_signs_exclusive hinc hC_ab hA_ab
  have hpos : 0 < Real.sin ρ := Real.sin_pos_of_pos_of_lt_pi hρpos hρlt
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

/-- **Excircles B and C are genuinely distinct.**  They agree on the `b`–`c` relation, so
they are told apart on the `a`–`c` relation: excircle B returns `⟪O,Na⟫ = ⟪O,Nc⟫`, whereas
excircle C's pair `⟪O,Na⟫ = ⟪O,Nb⟫`, `⟪O,Nb⟫ = -⟪O,Nc⟫` forces `⟪O,Na⟫ = -⟪O,Nc⟫`.  On a
nondegenerate radius these are incompatible, so excircles B and C are different circles. -/
theorem excircleB_excircleC_distinct {Na Nb Nc O : E} {ρ : ℝ}
    (hinc : SphericalIncircle Na Nb Nc O ρ)
    (hρpos : 0 < ρ) (hρlt : ρ < Real.pi)
    (hB_ac : (⟪O, Na⟫ : ℝ) = ⟪O, Nc⟫)
    (hC_ab : (⟪O, Na⟫ : ℝ) = ⟪O, Nb⟫)
    (hC_bc : (⟪O, Nb⟫ : ℝ) = -⟪O, Nc⟫) :
    False := by
  have hC_ac : (⟪O, Na⟫ : ℝ) = -⟪O, Nc⟫ := by linarith
  have h0 : Real.sin ρ = 0 := incircle_excircle_ac_signs_exclusive hinc hB_ac hC_ac
  have hpos : 0 < Real.sin ρ := Real.sin_pos_of_pos_of_lt_pi hρpos hρlt
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

end FeuerbachsTheoremOQ04
