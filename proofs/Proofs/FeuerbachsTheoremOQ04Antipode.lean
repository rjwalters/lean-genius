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

The core antipodal primitives `onSphere_neg`, `scos_neg_right` and `sdist_antipode`
now live in the *merged* file `Proofs.FeuerbachsTheoremOQ04` (they were absorbed there
alongside `sCircle_antipodal_center`); this file reuses them and supplies the
remaining antipodal-symmetry layer:

* `scos_neg_left` — the spherical cosine flips sign in the left slot under antipode
  (`⟪−P, Q⟫ = −⟪P, Q⟫`), the companion of the merged `scos_neg_right`.
* `scos_neg_neg` — negating *both* points preserves the spherical cosine.
* `sdist_neg_neg` — the antipodal map is a spherical isometry
  (`sdist (−P) (−Q) = sdist P Q`).
* `sCircle_neg_centre` — the **two-pole identity** `sCircle O ρ = sCircle (−O) (π − ρ)`:
  a spherical circle is centred on either pole, with complementary angular radius.
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

/-- **The antipodal map is a spherical isometry.**  Negating both points leaves the spherical
distance unchanged: `sdist (−P) (−Q) = sdist P Q`.  Since `sdist = arccos ∘ ⟪·,·⟫` and the two
inner-product sign flips cancel (`⟪−P, −Q⟫ = ⟪P, Q⟫`), the arccos argument is unchanged.  The
distance form of `scos_neg_neg`; makes precise that the antipodal involution acts on the model
sphere as a distance-preserving symmetry. -/
theorem sdist_neg_neg (P Q : E) : sdist (-P) (-Q) = sdist P Q := by
  unfold sdist; rw [inner_neg_left, inner_neg_right, neg_neg]

/-- **The two-pole identity.**  A spherical circle has two centres: the angular-radius-`ρ`
circle about a model point `O` is the *same set* as the angular-radius-`(π − ρ)` circle about
the antipodal pole `−O`.  Proof: a point `P` lies on `sCircle (−O) (π − ρ)` iff
`scos P (−O) = cos (π − ρ)`, i.e. `−scos P O = −cos ρ`, i.e. `scos P O = cos ρ`, the defining
condition of `sCircle O ρ`. -/
theorem sCircle_neg_centre (O : E) (ρ : ℝ) :
    sCircle O ρ = sCircle (-O) (Real.pi - ρ) := by
  ext P
  simp only [sCircle, Set.mem_setOf_eq, scos_neg_right, Real.cos_pi_sub, neg_inj]

end FeuerbachsTheoremOQ04
