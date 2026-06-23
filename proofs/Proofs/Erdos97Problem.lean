/-
# Erdős Problem #97: Equidistant Vertices in Convex Polygons

Does every convex polygon have a vertex with no other 4 vertices equidistant
from it?

**Status**: OPEN (for k = 4). Prize: $100.

**History**:
- Erdős originally conjectured (1946) that k = 3 holds.
- Danzer (1987) disproved the k = 3 conjecture with a 9-point convex polygon
  where every vertex has exactly 3 equidistant neighbors.
- Fishburn and Reeds (1992) found a convex 20-gon where every vertex has
  3 other vertices at UNIT distance (a stronger result).
- The k = 4 case remains open.

**References**:
- Erdős (1946): On sets of distances of n points. Amer. Math. Monthly 53, 248–250.
- Danzer (1987): In "Intuitive geometry" (Siófok, 1985), pp. 167–177.
- Fishburn and Reeds (1992): Unit distances between vertices of a convex polygon.
  Comput. Geom. 2, 81–91.
- https://erdosproblems.com/97
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Independent
import Mathlib.Tactic

/-- Abbreviation for the Euclidean plane. -/
abbrev ℝ² := EuclideanSpace ℝ (Fin 2)

open EuclideanGeometry

namespace Erdos97

/- ## Core Definitions -/

/--
A set of points A has **n equidistant points at p** if there exist at least
n other points in A that are equidistant from p (at some positive radius r).
-/
def HasNEquidistantPointsAt (n : ℕ) (A : Finset ℝ²) (p : ℝ²) : Prop :=
  ∃ r : ℝ, r > 0 ∧ (A.filter fun q ↦ dist p q = r).card ≥ n

/--
A set A has the **n-equidistant property** if every point in A has at least
n other points equidistant from it (at some, possibly vertex-dependent, radius).
-/
def HasNEquidistantProperty (n : ℕ) (A : Finset ℝ²) : Prop :=
  ∀ p ∈ A, HasNEquidistantPointsAt n A p

/--
A set A has the **n-unit-distance property** if every point in A has at least
n other points at unit distance from it.
-/
def HasNUnitDistanceProperty (n : ℕ) (A : Finset ℝ²) : Prop :=
  ∀ p ∈ A, n ≤ (A.filter fun q ↦ dist p q = 1).card

/- ## Main Conjecture -/

/--
**Erdős Problem #97 (OPEN, prize $100)**

Does every finite set of points in convex position fail the 4-equidistant
property? That is: must some vertex have fewer than 4 equidistant neighbors?

Equivalently: is there no convex polygon where every vertex has 4 other
vertices equidistant from it?
-/
@[simp]
def Erdos97Conjecture : Prop :=
  ∀ A : Finset ℝ², A.Nonempty → ConvexIndep id (A : Finset ℝ²) →
    ¬HasNEquidistantProperty 4 A

/- ## Solved Variants -/

/--
**Danzer's Counterexample (1987)**

There exists a convex polygon on 9 points where every vertex has 3 other
vertices equidistant from it. This disproves Erdős's original k = 3 conjecture.

Note: the equidistance radius varies by vertex (this is "equidistant" in the
sense of "same distance from that specific vertex", not a single global distance).
The formal-conjectures project gives explicit coordinates involving multiples of √3.
-/
axiom danzer_counterexample :
  ∃ A : Finset ℝ², A.card = 9 ∧
    ConvexIndep id (A : Finset ℝ²) ∧
    HasNEquidistantProperty 3 A

/--
The k = 3 case of the original Erdős conjecture is FALSE.
Witnessed by Danzer's 9-point construction.
-/
theorem erdos_97_k3_false :
    ¬(∀ A : Finset ℝ², A.Nonempty → ConvexIndep id (A : Finset ℝ²) →
        ¬HasNEquidistantProperty 3 A) := by
  obtain ⟨A, hcard, hconv, hequi⟩ := danzer_counterexample
  intro h
  have hne : A.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    simp [hempty] at hcard
  exact h A hne hconv hequi

/--
**Fishburn–Reeds Unit Distance Example (1992)**

There exists a convex polygon on 20 points where every vertex has 3 other
vertices at unit distance from it. This strengthens Danzer: the common
distance is fixed (= 1) rather than vertex-dependent.
-/
axiom fishburn_reeds_example :
  ∃ A : Finset ℝ², A.card = 20 ∧
    ConvexIndep id (A : Finset ℝ²) ∧
    HasNUnitDistanceProperty 3 A

/--
**Fishburn–Reeds Minimality (1992)**

20 is the smallest n for which a convex n-gon can have 3 unit-distance
neighbors at every vertex.
-/
axiom fishburn_reeds_minimal :
  (∀ A : Finset ℝ², A.card < 20 →
    ConvexIndep id (A : Finset ℝ²) →
    ¬HasNUnitDistanceProperty 3 A) ∧
  (∃ A : Finset ℝ², A.card = 20 ∧
    ConvexIndep id (A : Finset ℝ²) ∧
    HasNUnitDistanceProperty 3 A)

/- ## Stronger Conjecture -/

/--
**General k Conjecture (OPEN)**

Does there exist some k for which every convex polygon has a vertex with
no k equidistant neighbors? If true, this would give a universal bound on
the equidistance number of convex polygons.
-/
def GeneralKConjecture : Prop :=
  ∃ k : ℕ, ∀ A : Finset ℝ², A.Nonempty →
    ConvexIndep id (A : Finset ℝ²) →
    ¬HasNEquidistantProperty k A

/--
The main conjecture (k = 4) implies the general k conjecture.
-/
theorem main_implies_general (h : Erdos97Conjecture) : GeneralKConjecture :=
  ⟨4, h⟩

/- ## Why Convexity Matters -/

/--
Without convexity, there is no universal bound: for any k, there exist
k-regular configurations. This is witnessed by hypercube-like constructions.
-/
axiom no_bound_without_convexity :
  ∀ k : ℕ, ∃ A : Finset ℝ², HasNEquidistantProperty k A

end Erdos97
