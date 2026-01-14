/-
Erdős Problem #97: Equidistant Vertices in Convex Polygons

Does every convex polygon have a vertex with no other 4 vertices equidistant from it?

**Status**: OPEN (for k = 4)

**Solved Variants**:
- k = 3: NO - Danzer's 9-point counterexample (1987)
- k = 3 unit distance: NO - Fishburn-Reeds 20-point example (1992)

**History**:
- Erdős originally conjectured k = 3 (1946)
- Danzer disproved k = 3 (convex 9-gon with 3 equidistant from each vertex)
- The k = 4 case remains open

Reference: https://erdosproblems.com/97
-/

import Mathlib

open Finset
open scoped EuclideanGeometry

namespace Erdos97

/-!
## Background

This problem concerns the equidistance structure of convex polygons.

For each vertex of a convex polygon, we ask: how many other vertices can be
at the same distance from it? Erdős conjectured this should be bounded.

Danzer found a surprising counterexample for k = 3: a convex 9-gon where
every vertex has 3 other vertices equidistant from it.
-/

/--
The **distance** between two points in ℝ².
-/
noncomputable def dist' (p q : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  ‖p - q‖

/--
A point p has **k equidistant neighbors** in A if there exists a distance r
such that at least k points of A are at distance r from p.
-/
def hasKEquidistantAt (k : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  ∃ r : ℝ, r > 0 ∧ k ≤ (A.filter fun q => dist' p q = r).card

/--
A set A has the **k-equidistant property** if every point in A has at least
k other points equidistant from it.
-/
def hasKEquidistantProperty (k : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, hasKEquidistantAt k A p

/--
A point p has **k unit-distance neighbors** in A if at least k points of A
are at distance 1 from p.
-/
def hasKUnitDistanceAt (k : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2)))
    (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  k ≤ (A.filter fun q => dist' p q = 1).card

/--
A set A has the **k-unit-distance property** if every point in A has at least
k other points at unit distance from it.
-/
def hasKUnitDistanceProperty (k : ℕ) (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, hasKUnitDistanceAt k A p

/--
A set of points is in **convex position** if no point is in the convex hull
of the others. Equivalently, they form the vertices of a convex polygon.
-/
def isConvexPosition (A : Finset (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ (A.erase p : Set (EuclideanSpace ℝ (Fin 2)))

/-!
## The Main Question

Erdős asked whether every convex polygon has a vertex with no 4 vertices
equidistant from it. This remains OPEN.
-/

/--
**Erdős Problem #97 (OPEN)**

Does every convex polygon have a vertex with no 4 vertices equidistant from it?

Equivalently: does every convex n-gon fail the 4-equidistant property?

We state this without asserting its truth.
-/
def Erdos97Question : Prop :=
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.Nonempty → isConvexPosition A → ¬hasKEquidistantProperty 4 A

/-!
## Danzer's Counterexample (k = 3)

Danzer found a convex 9-gon where every vertex has 3 other vertices
equidistant from it. This disproves Erdős's original conjecture for k = 3.
-/

/--
**Danzer's Counterexample (1987)**

There exists a convex polygon on 9 points where every vertex has 3 other
vertices equidistant from it.

Note: the equidistance radius varies by vertex.
-/
axiom danzerCounterexample :
  ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = 9 ∧ isConvexPosition A ∧ hasKEquidistantProperty 3 A

/--
Danzer's 9 points can be constructed explicitly. The vertices form three
groups of three, arranged symmetrically around an equilateral triangle.
-/
def danzerPoints : Finset (EuclideanSpace ℝ (Fin 2)) :=
  -- The exact construction involves specific rational multiples of √3
  -- See formal-conjectures for the explicit coordinates
  sorry

/-!
## Fishburn-Reeds Result (Unit Distance)

Fishburn and Reeds found a convex 20-gon where every vertex has 3 other
vertices at UNIT distance. This is stronger than Danzer (fixed distance).
-/

/--
**Fishburn-Reeds (1992)**

There exists a convex polygon on 20 points where every vertex has 3 other
vertices at unit distance from it.
-/
axiom fishburnReedsExample :
  ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = 20 ∧ isConvexPosition A ∧ hasKUnitDistanceProperty 3 A

/--
**Fishburn-Reeds Minimality (1992)**

20 is the minimum n for a convex n-gon with a cut having 3 unit distances
on both sides.
-/
axiom fishburnReedsMinimal :
  ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card < 20 → isConvexPosition A → ¬hasKUnitDistanceProperty 3 A

/-!
## The General k Question

Erdős also asked: is there ANY k for which every convex polygon has a vertex
with no k vertices equidistant?
-/

/--
**General k Conjecture (OPEN)**

Does there exist some k such that every convex polygon has a vertex with
no k vertices equidistant from it?

This would give a universal bound on equidistant sets in convex polygons.
-/
def GeneralKConjecture : Prop :=
  ∃ k : ℕ, ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.Nonempty → isConvexPosition A → ¬hasKEquidistantProperty k A

/-!
## Connection to Problem #96

If the k = 4 conjecture holds, it would give bounds on the unit distance
problem for convex polygons (Problem #96).
-/

/--
If the k-equidistant conjecture holds for k+1, then by induction we get
an upper bound of kn for the number of unit distances in a convex n-gon.
-/
theorem kEquidistant_implies_unitDistance_bound (k : ℕ)
    (h : ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      A.Nonempty → isConvexPosition A → ¬hasKEquidistantProperty (k + 1) A) :
    ∀ A : Finset (EuclideanSpace ℝ (Fin 2)),
      isConvexPosition A →
      (A.filter fun p => ∃ q ∈ A, dist' p q = 1).card ≤ k * A.card := by
  sorry

/-!
## Non-Convex Case

Without convexity, there is no bound: hypercube graphs can be embedded
with all edges having unit length.
-/

/--
For any d, the d-dimensional hypercube graph can be embedded in ℝ² with
all edges having length 1, giving a non-convex polygon where every vertex
has d unit-distance neighbors.
-/
axiom hypercubeEmbedding :
  ∀ d : ℕ, ∃ A : Finset (EuclideanSpace ℝ (Fin 2)),
    A.card = 2^d ∧ hasKUnitDistanceProperty d A

/-!
## Historical Notes

This problem illustrates the surprising richness of convex polygon geometry.
Erdős's original conjecture (k = 3) seemed natural but was false. The
corrected conjecture (k = 4) remains open after decades.

The explicit Danzer construction uses 9 points arranged in 3 groups of 3,
with careful coordinate choices involving √3.
-/

end Erdos97
