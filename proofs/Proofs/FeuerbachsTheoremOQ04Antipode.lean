/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): the antipodal-pole layer

This companion file to `Proofs.FeuerbachsTheoremOQ04` adds the **two-pole description of a
spherical circle**.  Unlike a Euclidean circle, a spherical circle has *two* centres: the
two poles of the plane through it.  Concretely, the spherical circle of angular radius `ρ`
about a model point `O` is the *same* set of points as the circle of angular radius `π − ρ`
about the antipode `−O`.  This redundancy is exactly what a spherical incircle / nine-point
construction must keep track of (each "centre" of a configuration circle comes with its
antipodal twin), so isolating it as a verified lemma keeps later tangency bookkeeping honest.

Everything is built on the *merged* metric/circle API of `Proofs.FeuerbachsTheoremOQ04`
(`OnSphere`, `scos`, `sdist`, `sCircle`); this file adds no axioms and no sorries.

## What this file proves (0 axioms, 0 sorries)

* `onSphere_neg` — the antipode of a model point is a model point (`‖−P‖ = ‖P‖`).
* `scos_neg_right`, `scos_neg_left` — the spherical cosine flips sign under antipode
  (`⟪P, −Q⟫ = −⟪P, Q⟫`), the algebraic source of the pole swap.
* `sdist_antipode` — a model point and its antipode are at the maximal spherical distance
  `π` (`arccos (−1)`).
* `sCircle_neg_centre` — the **two-pole identity** `sCircle O ρ = sCircle (−O) (π − ρ)`:
  a spherical circle is centred on either pole, with complementary angular radius.
* `sdist_neg_right`, `sdist_neg_left` — antipode complements the spherical distance
  (`sdist P (−Q) = π − sdist P Q`), and `sdist_neg_neg` — the antipodal map is an isometry
  (`sdist (−P) (−Q) = sdist P Q`).
* `externallyTangent_iff_internallyTangent_antipode` and its dual
  `internallyTangent_iff_externallyTangent_antipode` — the antipodal pole swap **exchanges
  the two tangency types in both directions**, a purely spherical effect with no Euclidean
  analogue.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The antipode of a model point is again a model point: negation preserves the unit norm. -/
theorem onSphere_neg {P : E} (hP : OnSphere P) : OnSphere (-P) := by
  unfold OnSphere at hP ⊢
  rw [norm_neg]; exact hP

/-- The spherical cosine flips sign in the right slot under the antipodal map: this is the
algebraic engine behind the pole swap, since `cos (π − ρ) = −cos ρ` matches `⟪P, −O⟫`. -/
theorem scos_neg_right (P Q : E) : scos P (-Q) = - scos P Q := by
  unfold scos; rw [inner_neg_right]

/-- The spherical cosine flips sign in the left slot under the antipodal map. -/
theorem scos_neg_left (P Q : E) : scos (-P) Q = - scos P Q := by
  unfold scos; rw [inner_neg_left]

/-- **A model point and its antipode are at maximal spherical distance `π`.**  The inner
product `⟪P, −P⟫ = −‖P‖² = −1`, and `arccos (−1) = π`. -/
theorem sdist_antipode {P : E} (hP : OnSphere P) : sdist P (-P) = Real.pi := by
  unfold sdist
  rw [inner_neg_right, real_inner_self_eq_norm_sq, hP, one_pow]
  exact Real.arccos_neg_one

/-- **The two-pole identity.**  A spherical circle has two centres: the angular-radius-`ρ`
circle about a model point `O` is the *same set* as the angular-radius-`(π − ρ)` circle about
the antipodal pole `−O`.  Proof: a point `P` lies on `sCircle (−O) (π − ρ)` iff
`scos P (−O) = cos (π − ρ)`, i.e. `−scos P O = −cos ρ`, i.e. `scos P O = cos ρ`, the defining
condition of `sCircle O ρ`. -/
theorem sCircle_neg_centre (O : E) (ρ : ℝ) :
    sCircle O ρ = sCircle (-O) (Real.pi - ρ) := by
  ext P
  simp only [sCircle, Set.mem_setOf_eq, scos_neg_right, Real.cos_pi_sub, neg_inj]

/-! ## Tangency under the antipodal map

The two-pole identity propagates to the tangency relations: replacing a circle's centre by
its antipodal pole (`O ↦ −O`, `ρ ↦ π − ρ`) leaves the *circle* unchanged but **swaps the two
tangency types**.  This is a purely spherical phenomenon — in the Euclidean plane a circle has
a single centre, so there is no antipodal twin and external/internal tangency are not related
by any centre swap. -/

/-- **Spherical distance under the antipodal map.**  Sending the second point to its antipode
complements the spherical distance: `sdist P (−Q) = π − sdist P Q`.  The metric counterpart of
`scos_neg_right`, via `arccos (−x) = π − arccos x`. -/
theorem sdist_neg_right (P Q : E) : sdist P (-Q) = Real.pi - sdist P Q := by
  unfold sdist
  rw [inner_neg_right, Real.arccos_neg]

/-- **External tangency is internal tangency to the antipodal twin.**  Two spherical circles
`(O₁, ρ₁)`, `(O₂, ρ₂)` whose angular radii satisfy `ρ₁ + ρ₂ ≤ π` are externally tangent iff
the first is *internally* tangent to the antipodal description `(−O₂, π − ρ₂)` of the second
circle (which, by `sCircle_neg_centre`, is the very same circle).  The sum bound `ρ₁ + ρ₂ ≤ π`
fixes the sign of `ρ₁ − (π − ρ₂) = ρ₁ + ρ₂ − π` so the internal `|ρ₁ − ρ₂'|` opens up to
`π − (ρ₁ + ρ₂)`, which the distance complement `sdist O₁ (−O₂) = π − sdist O₁ O₂` matches
exactly against `sdist O₁ O₂ = ρ₁ + ρ₂`.

There is no Euclidean analogue: a plane circle has one centre, so external and internal
tangency are genuinely distinct relations with no centre-swap bridge between them. -/
theorem externallyTangent_iff_internallyTangent_antipode
    (O₁ O₂ : E) {ρ₁ ρ₂ : ℝ} (hsum : ρ₁ + ρ₂ ≤ Real.pi) :
    ExternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ InternallyTangent O₁ ρ₁ (-O₂) (Real.pi - ρ₂) := by
  unfold ExternallyTangent InternallyTangent
  rw [sdist_neg_right, abs_of_nonpos (by linarith : ρ₁ - (Real.pi - ρ₂) ≤ 0)]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith

/-- **Spherical distance under antipode of the first point.**  The left-slot counterpart of
`sdist_neg_right`: `sdist (−P) Q = π − sdist P Q`, again via `arccos (−x) = π − arccos x`. -/
theorem sdist_neg_left (P Q : E) : sdist (-P) Q = Real.pi - sdist P Q := by
  unfold sdist
  rw [inner_neg_left, Real.arccos_neg]

/-- **The antipodal map is a spherical isometry.**  Negating *both* points leaves the
spherical distance unchanged (`sdist (−P) (−Q) = sdist P Q`): the two sign flips of the
inner product cancel.  This is why the antipodal map sends configurations to congruent
configurations, and is the metric reason the two single-circle pole swaps come in a matched
external/internal pair rather than a single rule. -/
theorem sdist_neg_neg (P Q : E) : sdist (-P) (-Q) = sdist P Q := by
  unfold sdist
  rw [inner_neg_left, inner_neg_right, neg_neg]

/-- **Internal tangency is external tangency to the antipodal twin** — the dual of
`externallyTangent_iff_internallyTangent_antipode`.  Replacing the second circle by its
antipodal description `(−O₂, π − ρ₂)` (the same circle, by `sCircle_neg_centre`) turns an
*internal* tangency into an *external* one.  Here the governing sign condition is `ρ₁ ≤ ρ₂`
(rather than the sum bound `ρ₁ + ρ₂ ≤ π` of the external case): it fixes the sign of
`ρ₁ − ρ₂` so the internal `|ρ₁ − ρ₂|` opens to `ρ₂ − ρ₁`, which the distance complement
`sdist O₁ (−O₂) = π − sdist O₁ O₂` matches against the external sum `ρ₁ + (π − ρ₂)`.

Together with the external→internal direction this shows the antipodal pole swap *exchanges*
the two tangency types in both directions — a purely spherical effect with no Euclidean
analogue (a plane circle has a single centre and no antipodal twin). -/
theorem internallyTangent_iff_externallyTangent_antipode
    (O₁ O₂ : E) {ρ₁ ρ₂ : ℝ} (hle : ρ₁ ≤ ρ₂) :
    InternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ ExternallyTangent O₁ ρ₁ (-O₂) (Real.pi - ρ₂) := by
  unfold InternallyTangent ExternallyTangent
  rw [sdist_neg_right, abs_of_nonpos (by linarith : ρ₁ - ρ₂ ≤ 0)]
  constructor
  · intro h; rw [h]; ring
  · intro h; linarith

end FeuerbachsTheoremOQ04
