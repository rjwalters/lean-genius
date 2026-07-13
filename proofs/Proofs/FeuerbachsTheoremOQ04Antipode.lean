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

The core antipodal primitives `onSphere_neg`, `scos_neg_right`, `sdist_antipode` and the
single/double-slot distance laws `sdist_neg_left`, `sdist_neg_right`, `sdist_neg_neg` now
live in the *merged* file `Proofs.FeuerbachsTheoremOQ04` (absorbed there alongside
`sCircle_antipodal_center`); this file reuses them and supplies the remaining
antipodal-symmetry layer:

* `scos_neg_left` — the spherical cosine flips sign in the left slot under antipode
  (`⟪−P, Q⟫ = −⟪P, Q⟫`), the companion of the merged `scos_neg_right`.
* `scos_neg_neg` — negating *both* points preserves the spherical cosine.
* `sCircle_neg_centre` — the **two-pole identity** `sCircle O ρ = sCircle (−O) (π − ρ)`:
  a spherical circle is centred on either pole, with complementary angular radius.
* `sdist_neg_left_add` — `sdist (−P) Q + sdist P Q = π`: a pole and its antipode are
  seen at supplementary distances from every point.
* `externallyTangent_iff_internallyTangent_neg_left` — the **tangency-type swap**: for
  `ρ₁ + ρ₂ ≤ π`, `(O₁, ρ₁)` and `(O₂, ρ₂)` are externally tangent iff the antipodal
  representation `(−O₁, π − ρ₁)` and `(O₂, ρ₂)` are internally tangent — the two-pole
  identity read at the level of tangency.
* `externallyTangent_neg_neg`, `internallyTangent_neg_neg` — **tangency is invariant
  under the antipodal isometry** (negating *both* centres), the WLOG hemisphere-normalising
  move for a coordinate Feuerbach argument.
* `externallyTangent_iff_internallyTangent_neg_right`,
  `internallyTangent_iff_externallyTangent_neg_left` — the right-slot and internal→external
  duals of the tangency-type swap, closing the full 2×2 external/internal × antipodal-slot
  symmetry algebra of the tangency predicates.

This file also repairs a build-drift duplicate: `sdist_neg_left/right/neg_neg` were later
absorbed into the merged file (#38132) but left declared here, so the (orphan) companion no
longer compiled; the stale copies are removed.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The spherical cosine flips sign in the left slot under the antipodal map. -/
theorem scos_neg_left (P Q : E) : scos (-P) Q = - scos P Q := by
  unfold scos; rw [inner_neg_left]

/-- **The antipodal map preserves the spherical cosine.**  Negating *both* points cancels the
two single-slot sign flips (`scos_neg_left`, `scos_neg_right`), so `scos (−P) (−Q) = scos P Q`:
the involution `P ↦ −P` is a symmetry of the spherical-cosine pairing.  The paired counterpart
of the individual slot-flip lemmas. -/
theorem scos_neg_neg (P Q : E) : scos (-P) (-Q) = scos P Q := by
  rw [scos_neg_left, scos_neg_right, neg_neg]

/-- **The two-pole identity.**  A spherical circle has two centres: the angular-radius-`ρ`
circle about a model point `O` is the *same set* as the angular-radius-`(π − ρ)` circle about
the antipodal pole `−O`.  Proof: a point `P` lies on `sCircle (−O) (π − ρ)` iff
`scos P (−O) = cos (π − ρ)`, i.e. `−scos P O = −cos ρ`, i.e. `scos P O = cos ρ`, the defining
condition of `sCircle O ρ`. -/
theorem sCircle_neg_centre (O : E) (ρ : ℝ) :
    sCircle O ρ = sCircle (-O) (Real.pi - ρ) := by
  ext P
  simp only [sCircle, Set.mem_setOf_eq, scos_neg_right, Real.cos_pi_sub, neg_inj]

/-- **A point and its antipode split the meridian.**  Adding the distance from `P`
to `Q` and from its antipode `−P` to `Q` always yields a half-turn `π`: the two
poles `P`, `−P` are diametrically opposite, so every `Q` sees them at
supplementary spherical distances.  Immediate from `sdist_neg_left`. -/
theorem sdist_neg_left_add (P Q : E) : sdist (-P) Q + sdist P Q = Real.pi := by
  rw [sdist_neg_left]; ring

/-- **External tangency is internal tangency of the antipodal centre.**  On the
sphere the internal/external tangency distinction is *representation-dependent*:
because a circle `(O₁, ρ₁)` is the same set as `(−O₁, π − ρ₁)`
(`sCircle_neg_centre`), the two circles `(O₁, ρ₁)` and `(O₂, ρ₂)` are externally
tangent exactly when `(−O₁, π − ρ₁)` and `(O₂, ρ₂)` are internally tangent.
Proof: `ExternallyTangent` reads `sdist O₁ O₂ = ρ₁ + ρ₂`, while
`InternallyTangent (−O₁) (π − ρ₁) O₂ ρ₂` reads `sdist (−O₁) O₂ = |(π − ρ₁) − ρ₂|`;
by `sdist_neg_left` the left side is `π − sdist O₁ O₂`, and since `ρ₁ + ρ₂ ≤ π`
(the range where external tangency is geometrically possible) the absolute value
is `π − (ρ₁ + ρ₂)`, so both equations say the same thing. -/
theorem externallyTangent_iff_internallyTangent_neg_left
    {O₁ O₂ : E} {ρ₁ ρ₂ : ℝ} (h : ρ₁ + ρ₂ ≤ Real.pi) :
    ExternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ InternallyTangent (-O₁) (Real.pi - ρ₁) O₂ ρ₂ := by
  unfold ExternallyTangent InternallyTangent
  rw [sdist_neg_left]
  have habs : |Real.pi - ρ₁ - ρ₂| = Real.pi - (ρ₁ + ρ₂) := by
    rw [abs_of_nonneg (by linarith)]; ring
  rw [habs]
  constructor
  · intro he; rw [he]
  · intro hi; linarith

/-- **The antipodal map preserves external tangency.**  Negating *both* centres —
the antipodal spherical isometry `sdist (−O₁) (−O₂) = sdist O₁ O₂`
(`sdist_neg_neg`) — leaves external tangency unchanged: `(−O₁, ρ₁)` and
`(−O₂, ρ₂)` are externally tangent iff `(O₁, ρ₁)` and `(O₂, ρ₂)` are.  This is
tangency invariance under the antipodal involution, the WLOG move a coordinate
Feuerbach argument uses to normalise a configuration centre to a chosen
hemisphere. -/
theorem externallyTangent_neg_neg (O₁ : E) (ρ₁ : ℝ) (O₂ : E) (ρ₂ : ℝ) :
    ExternallyTangent (-O₁) ρ₁ (-O₂) ρ₂ ↔ ExternallyTangent O₁ ρ₁ O₂ ρ₂ := by
  unfold ExternallyTangent; rw [sdist_neg_neg]

/-- **The antipodal map preserves internal tangency.**  Internal counterpart of
`externallyTangent_neg_neg`: negating both centres leaves internal tangency
unchanged, again because `sdist (−O₁) (−O₂) = sdist O₁ O₂` (`sdist_neg_neg`). -/
theorem internallyTangent_neg_neg (O₁ : E) (ρ₁ : ℝ) (O₂ : E) (ρ₂ : ℝ) :
    InternallyTangent (-O₁) ρ₁ (-O₂) ρ₂ ↔ InternallyTangent O₁ ρ₁ O₂ ρ₂ := by
  unfold InternallyTangent; rw [sdist_neg_neg]

/-- **External tangency is internal tangency of the antipodal centre (right slot).**
The right-slot companion of `externallyTangent_iff_internallyTangent_neg_left`,
reading the two-pole identity (`sCircle_neg_centre`) on the *second* circle: for
`ρ₁ + ρ₂ ≤ π`, `(O₁, ρ₁)` and `(O₂, ρ₂)` are externally tangent iff `(O₁, ρ₁)`
and the antipodal representation `(−O₂, π − ρ₂)` of the second circle are
internally tangent.  Proof: `sdist O₁ (−O₂) = π − sdist O₁ O₂` (`sdist_neg_right`)
and, in the geometrically admissible range `ρ₁ + ρ₂ ≤ π`, both defining equations
read `sdist O₁ O₂ = ρ₁ + ρ₂`. -/
theorem externallyTangent_iff_internallyTangent_neg_right
    {O₁ O₂ : E} {ρ₁ ρ₂ : ℝ} (h : ρ₁ + ρ₂ ≤ Real.pi) :
    ExternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ InternallyTangent O₁ ρ₁ (-O₂) (Real.pi - ρ₂) := by
  unfold ExternallyTangent InternallyTangent
  rw [sdist_neg_right]
  have habs : |ρ₁ - (Real.pi - ρ₂)| = Real.pi - (ρ₁ + ρ₂) := by
    rw [abs_of_nonpos (by linarith)]; ring
  rw [habs]
  constructor
  · intro he; rw [he]
  · intro hi; linarith

/-- **Internal tangency is external tangency of the antipodal centre (left slot).**
The internal→external dual of `externallyTangent_iff_internallyTangent_neg_left`:
when `ρ₂ ≤ ρ₁` (so the internal-tangency modulus is `ρ₁ − ρ₂`), `(O₁, ρ₁)` and
`(O₂, ρ₂)` are internally tangent iff the antipodal representation `(−O₁, π − ρ₁)`
and `(O₂, ρ₂)` are externally tangent.  Together with the three swaps above this
closes the full 2×2 external/internal × antipodal-slot symmetry algebra of the
tangency predicates.  Proof: `sdist (−O₁) O₂ = π − sdist O₁ O₂` (`sdist_neg_left`)
and both equations read `sdist O₁ O₂ = ρ₁ − ρ₂`. -/
theorem internallyTangent_iff_externallyTangent_neg_left
    {O₁ O₂ : E} {ρ₁ ρ₂ : ℝ} (hρ : ρ₂ ≤ ρ₁) :
    InternallyTangent O₁ ρ₁ O₂ ρ₂ ↔ ExternallyTangent (-O₁) (Real.pi - ρ₁) O₂ ρ₂ := by
  unfold InternallyTangent ExternallyTangent
  rw [sdist_neg_left, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ρ₁ - ρ₂)]
  constructor
  · intro hi; linarith
  · intro he; linarith

end FeuerbachsTheoremOQ04
