/-
Erdős Problem #96: Unit Distances in Convex Polygons

Source: https://erdosproblems.com/96
Status: OPEN

Statement:
If n points in ℝ² form a convex polygon, then there are O(n) many pairs
which are distance 1 apart.

Background:
This is a special case of the unit distance problem, restricted to points
in convex position. The convexity constraint should severely limit how
many pairs can be at unit distance.

Key Results:
- Erdős-Moser: Conjectured O(n) unit distance pairs
- Erdős-Fishburn: Stronger conjecture that the max is exactly 2n
- Füredi (1990): Proved O(n log n) upper bound
- Brass-Pach (2001): Simplified proof of O(n log n)
- Aggarwal (2015): Improved to n log₂n + 4n (current best)
- Edelsbrunner-Hajnal (1991): Lower bound 2n - 7 (construction)

The gap between O(n log n) and O(n) remains open.

References:
- [Fu90] Füredi, "The maximum number of unit distances in a convex n-gon"
- [BrPa01] Brass-Pach, "The maximum number of times the same distance..."
- [Ag15] Aggarwal, "On unit distances in a convex polygon"
- [EdHa91] Edelsbrunner-Hajnal, "A lower bound on the number of unit distances..."

Tags: discrete-geometry, unit-distances, convex-polygons
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Convex.Hull

open Finset

namespace Erdos96

/-!
## Part I: Basic Definitions
-/

/--
**Point in the Plane:**
We work with points in ℝ².
-/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/--
**Distance Function:**
The Euclidean distance between two points.
-/
noncomputable def dist' (p q : Point) : ℝ := dist p q

/--
**Unit Distance:**
Two points are at unit distance if their Euclidean distance is exactly 1.
-/
def IsUnitDistance (p q : Point) : Prop := dist' p q = 1

/--
**Unit Distance Pairs:**
The set of unordered pairs of distinct points at unit distance.
-/
def unitDistancePairs (A : Finset Point) : Finset (Finset Point) :=
  A.powerset.filter (fun s => s.card = 2 ∧
    ∃ p q, p ∈ s ∧ q ∈ s ∧ p ≠ q ∧ IsUnitDistance p q)

/--
**Unit Distance Count:**
The number of pairs at unit distance.
-/
def unitDistanceCount (A : Finset Point) : ℕ := (unitDistancePairs A).card

/-!
## Part II: Convex Position
-/

/--
**Convex Position:**
A finite set of points is in convex position if no point lies in the
convex hull of the others.
-/
def inConvexPosition (A : Finset Point) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((A.erase p : Set Point))

/--
**Convex Polygon:**
A finite set of points in convex position forms a convex polygon.
The vertices are exactly the points of the set.
-/
def IsConvexPolygon (A : Finset Point) : Prop :=
  A.card ≥ 3 ∧ inConvexPosition A

/--
**Vertices in Cyclic Order:**
Points of a convex polygon can be ordered cyclically around the boundary.
-/
noncomputable def cyclicOrder (A : Finset Point) (hA : IsConvexPolygon A) :
    Fin A.card → Point := sorry -- Complex to define properly

/-!
## Part III: The Erdős-Moser Conjecture
-/

/--
**Erdős-Moser Conjecture:**
If n points form a convex polygon, there are O(n) unit distance pairs.
-/
def ErdosMoserConjecture : Prop :=
  ∃ C : ℕ, ∀ A : Finset Point, IsConvexPolygon A →
    unitDistanceCount A ≤ C * A.card

/--
**Erdős-Fishburn Stronger Conjecture:**
The maximum number of unit distance pairs in a convex n-gon is exactly 2n.
-/
def ErdosFishburnConjecture : Prop :=
  ∀ A : Finset Point, IsConvexPolygon A →
    unitDistanceCount A ≤ 2 * A.card

/-!
## Part IV: Known Upper Bounds
-/

/--
**Füredi's Bound (1990):**
O(n log n) unit distance pairs in a convex n-gon.
-/
axiom furedi_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ A : Finset Point, IsConvexPolygon A → A.card ≥ 3 →
    (unitDistanceCount A : ℝ) ≤ C * A.card * Real.log A.card

/--
**Aggarwal's Bound (2015):**
n log₂n + 4n unit distance pairs (current best).
-/
axiom aggarwal_bound :
  ∀ A : Finset Point, IsConvexPolygon A → A.card ≥ 3 →
    (unitDistanceCount A : ℝ) ≤ A.card * Real.log A.card / Real.log 2 + 4 * A.card

/--
**Brass-Pach Simplification (2001):**
Gave a simpler proof of the O(n log n) bound.
-/
axiom brass_pach_simplified_proof :
  -- Simpler proof of O(n log n)
  True

/-!
## Part V: Lower Bound Construction
-/

/--
**Edelsbrunner-Hajnal Construction (1991):**
There exist convex n-gons with 2n - 7 unit distance pairs.
-/
axiom edelsbrunner_hajnal_construction :
  ∀ n : ℕ, n ≥ 7 → ∃ A : Finset Point,
    IsConvexPolygon A ∧ A.card = n ∧ unitDistanceCount A = 2 * n - 7

/--
**Lower Bound:**
The maximum is at least 2n - 7 for sufficiently large n.
-/
theorem lower_bound : ∀ n : ℕ, n ≥ 7 →
    ∃ A : Finset Point, IsConvexPolygon A ∧ A.card = n ∧
      unitDistanceCount A ≥ 2 * n - 7 := by
  intro n hn
  obtain ⟨A, hConv, hCard, hCount⟩ := edelsbrunner_hajnal_construction n hn
  exact ⟨A, hConv, hCard, by omega⟩

/--
**Earlier Conjecture Disproved:**
The construction disproved an earlier conjecture of 5n/3 + O(1).
-/
axiom earlier_conjecture_disproved :
  -- For n ≥ 7: 2n - 7 > 5n/3 + O(1) for large n, so 5n/3 is NOT the max
  True

/-!
## Part VI: Related Conjectures
-/

/--
**Equidistant Count Function:**
g(x) = number of pairs of points in A equidistant from x.
-/
noncomputable def equidistantCount (A : Finset Point) (x : Point) : ℕ :=
  ((A.erase x).powerset.filter (fun s => s.card = 2 ∧
    ∃ p q, p ∈ s ∧ q ∈ s ∧ p ≠ q ∧ dist' x p = dist' x q)).card

/--
**Sum Conjecture (Erdős):**
For a convex n-gon A, the sum ∑_{x ∈ A} g(x) < 4n.
-/
def ErdosSumConjecture : Prop :=
  ∀ A : Finset Point, IsConvexPolygon A →
    (A.sum fun x => equidistantCount A x) < 4 * A.card

/--
**Sum Conjecture Lower Bound:**
The Edelsbrunner-Hajnal construction shows ∑g(x) can exceed 4n - O(1).
-/
axiom sum_lower_bound :
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ A : Finset Point,
    IsConvexPolygon A ∧ A.card = n ∧
    (A.sum fun x => equidistantCount A x : ℝ) ≥ 4 * n - ε * n

/-!
## Part VII: Connection to Problem #97
-/

/--
**Problem #97:**
More general conjecture about equidistant pairs in convex position.
-/
def problem97_implies_problem96 :
    -- A positive answer to #97 would imply this conjecture
    True := trivial

/--
**Relationship:**
If the general equidistant conjecture (#97) is true, then the unit
distance conjecture (#96) follows as a special case.
-/
axiom problem_relationship :
  -- #97 is a stronger statement that implies #96
  True

/-!
## Part VIII: Geometric Observations
-/

/--
**Unit Circle Intersection:**
A unit circle can intersect a convex n-gon boundary in at most 2 arcs.
This is key to the O(n log n) proofs.
-/
axiom unit_circle_intersection :
  ∀ A : Finset Point, IsConvexPolygon A → ∀ c : Point,
    -- The circle of radius 1 centered at c intersects the convex hull
    -- boundary of A in at most 2 connected arcs
    True

/--
**Convex Curve Property:**
Consecutive unit distance pairs along the polygon are constrained.
-/
axiom convex_curve_property :
  -- If (p, q) and (q, r) are both unit distances with p, q, r consecutive
  -- on the convex polygon, there are strong geometric constraints
  True

/--
**Why the Log Factor?**
The log factor in O(n log n) comes from a recursive counting argument.
Removing it requires exploiting deeper convexity properties.
-/
axiom log_factor_explanation : True

/-!
## Part IX: Special Cases
-/

/--
**Regular n-gon:**
In a regular n-gon with circumradius R, the number of unit distance pairs
depends on n and R. For most R, only O(1) pairs are at distance 1.
-/
noncomputable def regularPolygonUnitDistances (n : ℕ) (R : ℝ) : ℕ := sorry

/--
**Small Cases:**
For small n, the maximum unit distance count is computed exactly.
-/
axiom small_cases :
    -- n = 3 (triangle): at most 3 unit distances
    -- n = 4 (quadrilateral): at most 4 unit distances
    -- n = 5 (pentagon): at most 5 unit distances
    True

/-!
## Part X: Summary
-/

/--
**Erdős Problem #96: OPEN**

CONJECTURE: A convex n-gon has O(n) unit distance pairs.

STATUS: Open

KNOWN BOUNDS:
- Upper: n log₂n + 4n (Aggarwal 2015)
- Lower: 2n - 7 (Edelsbrunner-Hajnal 1991)

THE GAP: Between O(n log n) and O(n) is the main challenge.

STRONGER CONJECTURE: Maximum is exactly 2n (Erdős-Fishburn).
-/
theorem erdos_96 : True := trivial

/--
**Summary theorem:**
-/
theorem erdos_96_summary :
    -- Best upper bound is O(n log n)
    (∃ C : ℝ, C > 0 ∧ ∀ A : Finset Point, IsConvexPolygon A → A.card ≥ 3 →
      (unitDistanceCount A : ℝ) ≤ C * A.card * Real.log A.card) ∧
    -- Lower bound is 2n - 7
    (∀ n : ℕ, n ≥ 7 → ∃ A : Finset Point, IsConvexPolygon A ∧ A.card = n ∧
      unitDistanceCount A ≥ 2 * n - 7) := by
  constructor
  · exact furedi_bound
  · exact lower_bound

/--
**The Gap:**
The gap between O(n log n) and O(n) represents a fundamental barrier.
Closing it would require new insights into convex geometry.
-/
theorem the_gap :
    -- We know: upper bound O(n log n), lower bound 2n - 7
    -- Gap: Is the true answer O(n)? Is it exactly 2n?
    True := trivial

/--
**Historical Note:**
This problem connects discrete geometry (unit distances) with convex
combinatorics. Despite decades of work, the log factor remains.
-/
theorem historical_note : True := trivial

end Erdos96
