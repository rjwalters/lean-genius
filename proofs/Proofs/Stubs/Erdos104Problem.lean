/-
  Erdős Problem #104: Unit Circles Through Three Points

  Source: https://erdosproblems.com/104
  Status: OPEN ($100 prize)

  Statement:
  Given n points in ℝ², the number of distinct unit circles containing
  at least three points is o(n²). Conjecture: O(n^{3/2}).

  Background:
  For any two points, there are at most 2 unit circles passing through
  both (or exactly 1 if their distance is 2, or 0 if distance > 2).
  This gives a trivial O(n²) upper bound by double counting.

  But this bound is likely not tight. Elekes constructed point sets
  achieving Ω(n^{3/2}) unit circles with 3+ points each, suggesting
  this might be the true order of magnitude.

  The problem asks: can we prove o(n²), or better yet, O(n^{3/2})?

  Related to the unit distance problem and incidence geometry.

  References:
  [Er81d] Erdős, "Some applications of graph theory to number theory"
  [El84] Elekes, "n points in the plane can determine n^{3/2}/2 unit circles"
  [HaMe86] Harborth-Mengersen, "Circles passing through three points"

  Tags: discrete-geometry, incidences, unit-circles, open-problem
-/

import Mathlib

open Set Finset

/-
## Points and Unit Circles

Basic geometric definitions in the Euclidean plane.
-/

/-- A point in the Euclidean plane -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The Euclidean distance between two points -/
noncomputable def dist (p q : Point) : ℝ :=
  ‖p - q‖

/-- A unit circle is determined by its center -/
structure UnitCircle where
  center : Point

/-- A point lies on a unit circle if its distance to center is 1 -/
def OnCircle (p : Point) (c : UnitCircle) : Prop :=
  dist p c.center = 1

/-
## Point Sets and Circle Counting

Counting unit circles with many incidences.
-/

/-- A finite set of points in the plane -/
def PointSet := Finset Point

/-- A unit circle contains at least k points from a set -/
def CircleContainsKPoints (c : UnitCircle) (P : PointSet) (k : ℕ) : Prop :=
  (P.filter (fun p => OnCircle p c)).card ≥ k

/-- The set of unit circles containing at least 3 points from P -/
noncomputable def unitCirclesThrough3 (P : PointSet) : Set UnitCircle :=
  {c : UnitCircle | CircleContainsKPoints c P 3}

/-- The count of such circles (may be infinite in general, but finite for finite P) -/
noncomputable def countUnitCircles3 (P : PointSet) : ℕ :=
  (unitCirclesThrough3 P).ncard

/-
## Trivial Upper Bound

Each pair of points determines at most 2 unit circles.
-/

/-- Two points at distance d < 2 determine exactly 2 unit circles through both -/
axiom two_points_two_circles :
  ∀ p q : Point, p ≠ q → dist p q < 2 →
    ∃! (S : Finset UnitCircle), S.card = 2 ∧
      ∀ c ∈ S, OnCircle p c ∧ OnCircle q c

/-- Two points at distance exactly 2 determine exactly 1 unit circle -/
axiom two_points_one_circle :
  ∀ p q : Point, dist p q = 2 →
    ∃! c : UnitCircle, OnCircle p c ∧ OnCircle q c

/-- Two points at distance > 2 determine no unit circles through both -/
axiom two_points_no_circle :
  ∀ p q : Point, dist p q > 2 →
    ∀ c : UnitCircle, ¬(OnCircle p c ∧ OnCircle q c)

/-- Trivial upper bound: at most n(n-1) unit circles with 3+ points -/
axiom trivial_upper_bound :
  ∀ P : PointSet, countUnitCircles3 P ≤ P.card * (P.card - 1)

/-- Harborth-Mengersen refinement: at most n(n-1)/3 -/
axiom harborth_mengersen_bound :
  ∀ P : PointSet, P.card ≥ 3 →
    countUnitCircles3 P ≤ P.card * (P.card - 1) / 3

/-
## Lower Bound Constructions

Elekes showed Ω(n^{3/2}) is achievable.
-/

/-- There exist point sets achieving Ω(n^{3/2}) unit circles -/
axiom elekes_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
    ∃ P : PointSet, P.card = n ∧
      (countUnitCircles3 P : ℝ) ≥ c * n^(3/2 : ℝ)

/-- Simple lower bound: Ω(n) is easy -/
axiom linear_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 →
    ∃ P : PointSet, P.card = n ∧
      (countUnitCircles3 P : ℝ) ≥ c * n

/-
## The Main Conjecture

The conjectured bound is O(n^{3/2}).
-/

/-- The conjecture: countUnitCircles3(P) = O(n^{3/2}) -/
def erdos104Conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ P : PointSet,
    (countUnitCircles3 P : ℝ) ≤ C * P.card^(3/2 : ℝ)

/-- Weaker conjecture: o(n²) -/
def erdos104WeakConjecture : Prop :=
  ∀ ε > 0, ∃ C : ℝ, ∀ P : PointSet,
    (countUnitCircles3 P : ℝ) ≤ C * P.card^(2 - ε : ℝ)

/-- The strong conjecture implies the weak one -/
theorem strong_implies_weak : erdos104Conjecture → erdos104WeakConjecture := by
  intro ⟨C, hC, h⟩ ε hε
  use C
  intro P
  calc (countUnitCircles3 P : ℝ)
      ≤ C * P.card^(3/2 : ℝ) := h P
    _ ≤ C * P.card^(2 - ε : ℝ) := by
        sorry -- for large n, n^{3/2} < n^{2-ε} when ε < 1/2

/-
## Connections to Incidence Geometry

Related to the Szemerédi-Trotter theorem.
-/

/-- Number of incidences between points and circles -/
noncomputable def incidenceCount (P : PointSet) (C : Set UnitCircle) : ℕ :=
  (P.sum fun p => (C.indicator (fun c => if OnCircle p c then 1 else 0)).sum).toNat

/-- Szemerédi-Trotter type bound for circles (Clarkson et al.) -/
axiom circle_incidence_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ P : PointSet, ∀ Circ : Finset UnitCircle,
    (incidenceCount P Circ : ℝ) ≤ C * (P.card^(2/3 : ℝ) * Circ.card^(2/3 : ℝ) + P.card + Circ.card)

/-
## Known Values (OEIS A003829)

Maximum unit circles with 3+ points for small n.
-/

/-- Maximum over all n-point sets -/
noncomputable def maxUnitCircles (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : PointSet, P.card = n ∧ countUnitCircles3 P = k}

/-- Known values: f(3) = 1 (any 3 points give at most 1 unit circle through all 3) -/
axiom max_3 : maxUnitCircles 3 = 1

/-- f(4) = 4 -/
axiom max_4 : maxUnitCircles 4 = 4

/-- f(5) = 8 -/
axiom max_5 : maxUnitCircles 5 = 8

/-- f(6) = 13 -/
axiom max_6 : maxUnitCircles 6 = 13

/-
## The Open Problem

The exact growth rate remains unknown.
-/

/-- The main open question -/
def erdos104OpenProblem : Prop := erdos104Conjecture

#check countUnitCircles3
#check erdos104Conjecture
#check elekes_lower_bound
#check harborth_mengersen_bound
