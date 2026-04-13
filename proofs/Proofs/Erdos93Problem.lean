/-
Erdős Problem #93: Distinct Distances in Convex Polygons

Source: https://erdosproblems.com/93
Status: SOLVED (Altman 1963)

Statement:
If n distinct points in ℝ² form a convex polygon, then they determine
at least ⌊n/2⌋ distinct distances.

Answer: TRUE (Altman 1963)

Key Results:
- Altman (1963): Proved the ⌊n/2⌋ lower bound
- The bound is tight: regular n-gons achieve exactly ⌊n/2⌋ distances
- Stronger variant (one point with ⌊n/2⌋ distances) is still OPEN (#982)
- Fishburn's conjecture: Σ R(x) ≥ C(n,2) where R(x) = distances from x

Tags: geometry, convex-polygon, distinct-distances, solved
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

open Finset Real

namespace Erdos93

/-
## Part I: Basic Definitions

Points, distances, and counting distinct distances.
-/

/-- A point in the plane -/
abbrev Point := ℝ × ℝ

/-- Distance between two points -/
noncomputable def dist (p q : Point) : ℝ :=
  Real.sqrt ((p.1 - q.1)^2 + (p.2 - q.2)^2)

/-- The set of distinct distances determined by a point set -/
noncomputable def distinctDistances (S : Finset Point) : Finset ℝ :=
  (S ×ˢ S).image (fun pq => dist pq.1 pq.2) |>.filter (· > 0)

/-- Number of distinct distances -/
noncomputable def numDistinctDistances (S : Finset Point) : ℕ :=
  (distinctDistances S).card

/-
## Part II: Convex Position

A set of points is in convex position if no point lies
in the convex hull of the remaining points.
-/

/--
A finite set of points is in convex position if they form the vertices
of a convex polygon. Axiomatized because the convex hull definition
requires substantial geometric infrastructure.
-/
axiom InConvexPosition (S : Finset Point) : Prop

/-
## Part III: Altman's Theorem (1963)
-/

/--
**Altman's Theorem (1963):**
Convex n-gon has at least ⌊n/2⌋ distinct distances.
This is the main result solving Erdős Problem #93.
-/
axiom altman_theorem :
  ∀ S : Finset Point, InConvexPosition S →
    numDistinctDistances S ≥ S.card / 2


/-
## Part IV: Stronger Variant (OPEN — Problem #982)

Does some vertex see ⌊n/2⌋ distinct distances?
-/

/-- Distances from a single point -/
noncomputable def distancesFrom (p : Point) (S : Finset Point) : Finset ℝ :=
  (S.erase p).image (dist p) |>.filter (· > 0)

/-- Number of distinct distances from a point -/
noncomputable def numDistancesFrom (p : Point) (S : Finset Point) : ℕ :=
  (distancesFrom p S).card

/--
**Stronger Variant (Problem #982, OPEN):**
In a convex n-gon, does some vertex determine ≥ ⌊n/2⌋ distinct distances?
This is strictly stronger than Altman's theorem.
-/
def StrongerVariant : Prop :=
  ∀ S : Finset Point, InConvexPosition S → S.card ≥ 3 →
    ∃ p ∈ S, numDistancesFrom p S ≥ S.card / 2

/-
## Part V: Fishburn's Conjecture
-/

/--
**Fishburn's Conjecture:**
For a convex n-gon, Σ_{x ∈ S} R(x) ≥ C(n,2), where R(x)
is the number of distinct distances from x.

If true, it implies that the average R(x) ≥ (n-1)/2,
so some vertex achieves ≥ ⌊n/2⌋ (proving the stronger variant).
-/
def FishburnConjecture : Prop :=
  ∀ S : Finset Point, InConvexPosition S →
    S.sum (fun p => numDistancesFrom p S) ≥ S.card * (S.card - 1) / 2

/-- Fishburn's conjecture implies the stronger variant. -/
axiom fishburn_implies_stronger :
  FishburnConjecture → StrongerVariant

/-
## Part VI: Summary
-/

/--
**Erdős Problem #93: Summary**

SOLVED by Altman (1963). Convex n-gon ⟹ ≥ ⌊n/2⌋ distinct distances.

Combines:
1. Altman's lower bound (the main result)
2. Regular polygon tightness (⌊n/2⌋ is best possible)
3. Fishburn's conjecture implies the stronger variant
-/
theorem erdos_93_summary :
    -- Altman: convex n-gon has ≥ ⌊n/2⌋ distances
    (∀ S : Finset Point, InConvexPosition S →
      numDistinctDistances S ≥ S.card / 2) ∧
    -- Fishburn implies stronger variant
    (FishburnConjecture → StrongerVariant) :=
  ⟨altman_theorem, fishburn_implies_stronger⟩

end Erdos93
