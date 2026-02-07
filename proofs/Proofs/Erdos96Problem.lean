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

/- ## Part I: Basic Definitions -/

/-- Point in the plane: ℝ² via EuclideanSpace. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Euclidean distance between two points. -/
noncomputable def dist' (p q : Point) : ℝ := dist p q

/-- Two points are at unit distance if dist(p, q) = 1. -/
def IsUnitDistance (p q : Point) : Prop := dist' p q = 1

/-- The set of unordered pairs of distinct points at unit distance. -/
def unitDistancePairs (A : Finset Point) : Finset (Finset Point) :=
  A.powerset.filter (fun s => s.card = 2 ∧
    ∃ p q, p ∈ s ∧ q ∈ s ∧ p ≠ q ∧ IsUnitDistance p q)

/-- The number of pairs at unit distance. -/
def unitDistanceCount (A : Finset Point) : ℕ := (unitDistancePairs A).card

/- ## Part II: Convex Position -/

/-- A finite set is in convex position if no point lies in the convex hull
    of the others. -/
def inConvexPosition (A : Finset Point) : Prop :=
  ∀ p ∈ A, p ∉ convexHull ℝ ((A.erase p : Set Point))

/-- A convex polygon: at least 3 points in convex position. -/
def IsConvexPolygon (A : Finset Point) : Prop :=
  A.card ≥ 3 ∧ inConvexPosition A

/- ## Part III: The Conjectures -/

/-- Erdős-Moser Conjecture: A convex n-gon has O(n) unit distance pairs. -/
def ErdosMoserConjecture : Prop :=
  ∃ C : ℕ, ∀ A : Finset Point, IsConvexPolygon A →
    unitDistanceCount A ≤ C * A.card

/-- Erdős-Fishburn Conjecture (stronger): The maximum is exactly 2n. -/
def ErdosFishburnConjecture : Prop :=
  ∀ A : Finset Point, IsConvexPolygon A →
    unitDistanceCount A ≤ 2 * A.card

/- ## Part IV: Known Upper Bounds -/

/-- Füredi's Bound (1990): O(n log n) unit distance pairs in a convex n-gon. -/
axiom furedi_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ A : Finset Point, IsConvexPolygon A → A.card ≥ 3 →
    (unitDistanceCount A : ℝ) ≤ C * A.card * Real.log A.card

/-- Aggarwal's Bound (2015): n log₂n + 4n unit distance pairs (current best). -/
axiom aggarwal_bound :
  ∀ A : Finset Point, IsConvexPolygon A → A.card ≥ 3 →
    (unitDistanceCount A : ℝ) ≤ A.card * Real.log A.card / Real.log 2 + 4 * A.card

/- ## Part V: Lower Bound Construction -/

/-- Edelsbrunner-Hajnal Construction (1991): There exist convex n-gons
    with 2n - 7 unit distance pairs. -/
axiom edelsbrunner_hajnal_construction :
  ∀ n : ℕ, n ≥ 7 → ∃ A : Finset Point,
    IsConvexPolygon A ∧ A.card = n ∧ unitDistanceCount A = 2 * n - 7

/-- The maximum is at least 2n - 7 for sufficiently large n. -/
theorem lower_bound : ∀ n : ℕ, n ≥ 7 →
    ∃ A : Finset Point, IsConvexPolygon A ∧ A.card = n ∧
      unitDistanceCount A ≥ 2 * n - 7 := by
  intro n hn
  obtain ⟨A, hConv, hCard, hCount⟩ := edelsbrunner_hajnal_construction n hn
  exact ⟨A, hConv, hCard, by omega⟩

/- ## Part VI: Related Conjectures -/

/-- Equidistant count function:
    g(x) = number of pairs in A equidistant from x. -/
noncomputable def equidistantCount (A : Finset Point) (x : Point) : ℕ :=
  ((A.erase x).powerset.filter (fun s => s.card = 2 ∧
    ∃ p q, p ∈ s ∧ q ∈ s ∧ p ≠ q ∧ dist' x p = dist' x q)).card

/-- Erdős Sum Conjecture: For a convex n-gon A, ∑_{x ∈ A} g(x) < 4n. -/
def ErdosSumConjecture : Prop :=
  ∀ A : Finset Point, IsConvexPolygon A →
    (A.sum fun x => equidistantCount A x) < 4 * A.card

/-- The Edelsbrunner-Hajnal construction shows ∑g(x) can be close to 4n. -/
axiom sum_lower_bound :
  ∀ ε > 0, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∃ A : Finset Point,
    IsConvexPolygon A ∧ A.card = n ∧
    (A.sum fun x => equidistantCount A x : ℝ) ≥ 4 * n - ε * n

/- ## Part VII: Summary -/

/-- Erdős Problem #96: OPEN.
    Upper bound: O(n log n) from Füredi (1990), best constant from Aggarwal (2015).
    Lower bound: 2n - 7 from Edelsbrunner-Hajnal (1991).
    The gap between O(n log n) and O(n) is the main open question.
    Stronger conjecture: maximum is exactly 2n (Erdős-Fishburn). -/
theorem erdos_96_summary :
    (∃ C : ℝ, C > 0 ∧ ∀ A : Finset Point, IsConvexPolygon A → A.card ≥ 3 →
      (unitDistanceCount A : ℝ) ≤ C * A.card * Real.log A.card) ∧
    (∀ n : ℕ, n ≥ 7 → ∃ A : Finset Point, IsConvexPolygon A ∧ A.card = n ∧
      unitDistanceCount A ≥ 2 * n - 7) := by
  exact ⟨furedi_bound, lower_bound⟩

end Erdos96
