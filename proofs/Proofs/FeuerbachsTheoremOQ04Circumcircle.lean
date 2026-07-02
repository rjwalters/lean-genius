/-
# Feuerbach's Theorem in Non-Euclidean Geometry (OQ-04): the spherical circumcircle

This companion file to `Proofs.FeuerbachsTheoremOQ04` supplies the **spherical
circumcircle**: for any three model points (unit vectors) `A, B, C` on a sphere of
dimension `≥ 2`, there is a centre `O` and angular radius `ρ` with all three lying on the
single spherical circle `sCircle O ρ` — equivalently, `O` is spherically equidistant from
`A, B, C`.

## Why this matters for Feuerbach

The spherical **nine-point circle** of a spherical triangle is the circumcircle of its
*medial triangle* (the triangle of the three side-midpoints).  Producing a circumcircle
through any three points is therefore the existence primitive underneath the nine-point
circle, exactly as the incircle / excircle existence lemmas (`sphericalIncircle_exists`,
`sphericalExcircle{A,B,C}_exists`) sit underneath the tritangent family.

## The construction

This is the spherical **perpendicular-bisector** argument, dual to the incenter one
(`sphericalIncircle_center_on_bisectors` / `sphericalIncircle_exists`).  There the centre was
equidistant from the three *side poles* `Na, Nb, Nc`; here it is equidistant from the three
*vertices* `A, B, C`.  The model points equidistant (equal `scos`) from `A` and `B` are
exactly those orthogonal to the pole `A − B` — a great circle, the spherical perpendicular
bisector of the segment `AB`.  The circumcentre is the common point of two such
perpendicular-bisector great circles (poles `A − B` and `B − C`), produced by the merged
`greatCircles_inter`; it then satisfies `scos A O = scos B O = scos C O`, and `ρ = arccos` of
that common cosine is the common spherical circumradius.

Everything is built on the *merged* API of `Proofs.FeuerbachsTheoremOQ04`
(`OnSphere`, `scos`, `sdist`, `sCircle`, `sGreatCircle`, `greatCircles_inter`, `cos_sdist`);
this file adds no axioms and no sorries.

## What this file proves (0 axioms, 0 sorries)

* `inner_sub_eq_zero_iff_scos_eq` — the **perpendicular-bisector characterisation**: a model
  point `O` is orthogonal to the pole `A − B` iff it is spherically equidistant (equal
  `scos`) from `A` and `B`.
* `sphericalCircumcircle_exists` — **existence of the circumcircle**: any three model points
  lie on a common spherical circle `sCircle O ρ`.
* `sphericalCircumcircle_equidistant` — the circumcentre is spherically equidistant from the
  three points: `sdist A O = sdist B O = sdist C O`.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ04

namespace FeuerbachsTheoremOQ04

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Perpendicular-bisector characterisation.**  A model point `O` is orthogonal to the
pole `A − B` exactly when it is spherically equidistant from `A` and `B`, i.e. has equal
spherical cosine to both.  The set of such `O` is the great circle with pole `A − B` — the
spherical perpendicular bisector of the segment `AB`. -/
theorem inner_sub_eq_zero_iff_scos_eq (A B O : E) :
    (⟪O, A - B⟫ : ℝ) = 0 ↔ scos A O = scos B O := by
  unfold scos
  rw [inner_sub_right, sub_eq_zero, real_inner_comm A O, real_inner_comm B O]

/-- **Existence of the spherical circumcircle.**  For any three model points `A, B, C` on a
sphere of dimension `≥ 2` (`finrank ℝ E > 2`) there is a centre `O` and angular radius `ρ`
with `A, B, C` all on the single spherical circle `sCircle O ρ`.  Construct `O` by
intersecting the two perpendicular-bisector great circles (poles `A − B`, `B − C`) via
`greatCircles_inter`; this forces `scos A O = scos B O = scos C O`, and `ρ = sdist A O`
realises the common circumradius (`cos ρ` equals that common cosine by `cos_sdist`). -/
theorem sphericalCircumcircle_exists [FiniteDimensional ℝ E] (A B C : E)
    (hA : OnSphere A) (hB : OnSphere B) (hC : OnSphere C)
    (hdim : 2 < Module.finrank ℝ E) :
    ∃ (O : E) (ρ : ℝ), OnSphere O ∧
      A ∈ sCircle O ρ ∧ B ∈ sCircle O ρ ∧ C ∈ sCircle O ρ := by
  obtain ⟨O, hO, _, hAB, hBC, _, _⟩ := greatCircles_inter (A - B) (B - C) hdim
  have eAB : scos A O = scos B O := (inner_sub_eq_zero_iff_scos_eq A B O).mp hAB.2
  have eBC : scos B O = scos C O := (inner_sub_eq_zero_iff_scos_eq B C O).mp hBC.2
  refine ⟨O, sdist A O, hO, ?_, ?_, ?_⟩
  · exact ⟨hA, by rw [cos_sdist A O hA hO]⟩
  · exact ⟨hB, by rw [cos_sdist A O hA hO]; exact eAB.symm⟩
  · exact ⟨hC, by rw [cos_sdist A O hA hO]; exact (eAB.trans eBC).symm⟩

/-- **The circumcentre is spherically equidistant from the three points.**  The centre `O`
produced above satisfies `sdist A O = sdist B O = sdist C O` — the defining property of a
circumcentre.  Immediate from the equal spherical cosines `scos A O = scos B O = scos C O`,
since `sdist · O = arccos (scos · O)`. -/
theorem sphericalCircumcircle_equidistant [FiniteDimensional ℝ E] (A B C : E)
    (hdim : 2 < Module.finrank ℝ E) :
    ∃ O : E, OnSphere O ∧ sdist A O = sdist B O ∧ sdist B O = sdist C O := by
  obtain ⟨O, hO, _, hAB, hBC, _, _⟩ := greatCircles_inter (A - B) (B - C) hdim
  have hAB' : (⟪A, O⟫ : ℝ) = ⟪B, O⟫ := (inner_sub_eq_zero_iff_scos_eq A B O).mp hAB.2
  have hBC' : (⟪B, O⟫ : ℝ) = ⟪C, O⟫ := (inner_sub_eq_zero_iff_scos_eq B C O).mp hBC.2
  refine ⟨O, hO, ?_, ?_⟩
  · unfold sdist; rw [hAB']
  · unfold sdist; rw [hBC']

end FeuerbachsTheoremOQ04
