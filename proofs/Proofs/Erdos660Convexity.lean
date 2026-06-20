/-
  Erdős Problem #660 — Convex-geometry infrastructure

  Source: https://erdosproblems.com/660  (distinct distances in convex polyhedra)

  The main file `Erdos660Problem.lean` scaffolds the open conjecture together with a
  number of explicit "special case" constructions (regular tetrahedron, cube,
  octahedron, dodecahedron, icosahedron). Each construction has to certify that its
  vertex set `S` satisfies `IsConvexPolyhedronVertices S`, i.e. that **every** point of
  `S` is an extreme point of `convexHull ℝ S`.

  For a *simplex* — an affinely independent vertex set, such as the 4 vertices of a
  regular tetrahedron — this reduces to the statement that an affinely independent
  family is *convex independent*: no vertex lies in the convex hull of the others.
  Mathlib records this as an open TODO:

      Mathlib/Analysis/Convex/Independent.lean (module docstring):
        "Prove `AffineIndependent.convexIndependent`. This requires some glue between
         `affineCombination` and `Finset.centerMass`."

  This file supplies exactly that missing lemma, via a short route that sidesteps the
  combination bookkeeping: a convex hull is contained in the affine span, and an
  affinely independent point is provably outside the affine span of the others
  (`AffineIndependent.notMem_affineSpan_diff`). Hence it is outside their convex hull,
  which is the definition of convex independence.

  The lemma is stated in the `AffineIndependent` namespace so that it is a drop-in for
  the Mathlib TODO and reusable beyond this problem.
-/

import Mathlib

open scoped Affine

namespace Erdos660

variable {𝕜 E ι : Type*}
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **An affinely independent family is convex independent.**

This is the lemma flagged as a TODO in `Mathlib/Analysis/Convex/Independent.lean`
(`AffineIndependent.convexIndependent`). The proof avoids the `affineCombination` /
`centerMass` glue mentioned there: convex hulls are contained in affine spans
(`convexHull_subset_affineSpan`), and an affinely independent point avoids the affine
span of the other points (`AffineIndependent.notMem_affineSpan_diff`); composing the
two gives that the point avoids the convex hull of the others, i.e. convex
independence (`convexIndependent_iff_notMem_convexHull_diff`). -/
theorem _root_.AffineIndependent.convexIndependent {p : ι → E}
    (hp : AffineIndependent 𝕜 p) : ConvexIndependent 𝕜 p := by
  rw [convexIndependent_iff_notMem_convexHull_diff]
  intro i s h
  exact hp.notMem_affineSpan_diff i s (convexHull_subset_affineSpan _ h)

/-- Set-indexed form: an affinely independent subset of a real vector space is convex
independent, i.e. no point lies in the convex hull of the others. -/
theorem convexIndependent_of_affineIndependent_set {s : Set E}
    (hs : AffineIndependent 𝕜 ((↑) : s → E)) :
    ConvexIndependent 𝕜 ((↑) : s → E) :=
  hs.convexIndependent

/-- Concrete consequence used by the simplex constructions: for an affinely
independent subset `s`, no point of `s` lies in the convex hull of the remaining
points. -/
theorem notMem_convexHull_diff_of_affineIndependent_set {s : Set E}
    (hs : AffineIndependent 𝕜 ((↑) : s → E)) {x : E} (hx : x ∈ s) :
    x ∉ convexHull 𝕜 (s \ {x}) :=
  (convexIndependent_set_iff_notMem_convexHull_diff.1 hs.convexIndependent) x hx

end Erdos660
