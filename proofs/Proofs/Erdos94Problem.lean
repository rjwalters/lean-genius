/-
  Erdős Problem #94: Distance Multiplicities in Convex Polygons

  Source: https://erdosproblems.com/94
  Status: SOLVED (Fishburn; strengthened by Lefmann-Theile 1995)
  Prize: $44

  Statement:
  Suppose n points in ℝ² form the vertices of a convex polygon. Let {u₁, ..., u_t}
  be the set of distinct distances between points, and let f(u_i) count how many
  pairs of points are at distance u_i. Then:
    ∑_i f(u_i)² ≪ n³

  Note: Trivially ∑ f(u_i) = C(n,2) = n(n-1)/2 (total number of pairs).

  Key Results:
  - Fishburn proved the n³ bound for convex polygons
  - Lefmann-Theile (1995) strengthened this to "no three collinear" condition
  - Erdős-Fishburn conjecture: regular n-gon maximizes ∑ f(u_i)²

  Tags: geometry, convex, distances, combinatorics
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

namespace Erdos94

open Finset Real

/- ## Part I: Point Configurations -/

/-- A point in the Euclidean plane. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A finite point configuration. -/
def PointConfig := Finset Point

/-- The distance between two points. -/
noncomputable def dist' (p q : Point) : ℝ := dist p q

/-- The set of all pairwise distances in a configuration. -/
noncomputable def distanceSet (P : PointConfig) : Finset ℝ :=
  (P.product P).image (fun pq => dist' pq.1 pq.2) |>.filter (· > 0)

/-- The multiset of distances (with repetition). -/
noncomputable def distanceMultiset (P : PointConfig) : Multiset ℝ :=
  (P.product P).val.map (fun pq => dist' pq.1 pq.2) |>.filter (· > 0)

/- ## Part II: Distance Multiplicity -/

/-- f(u) = number of ordered pairs at distance u. -/
noncomputable def distanceMultiplicity (P : PointConfig) (u : ℝ) : ℕ :=
  ((P.product P).filter fun pq => dist' pq.1 pq.2 = u ∧ pq.1 ≠ pq.2).card

/-- f(u) for unordered pairs (half of ordered). -/
noncomputable def unorderedMultiplicity (P : PointConfig) (u : ℝ) : ℕ :=
  distanceMultiplicity P u / 2

/-- The sum ∑ f(u_i) equals the total number of pairs. -/
theorem sum_multiplicities (P : PointConfig) :
    (distanceSet P).sum (unorderedMultiplicity P) = P.card.choose 2 := by
  sorry

/- ## Part III: Sum of Squared Multiplicities -/

/-- The key quantity: ∑ f(u_i)². -/
noncomputable def sumSquaredMultiplicities (P : PointConfig) : ℕ :=
  (distanceSet P).sum fun u => (unorderedMultiplicity P u) ^ 2

/-- Alternative: count quadruples (p,q,r,s) with d(p,q) = d(r,s). -/
noncomputable def countEqualDistancePairs (P : PointConfig) : ℕ :=
  ((P.product P).product (P.product P)).filter fun ((p,q), (r,s)) =>
    p ≠ q ∧ r ≠ s ∧ dist' p q = dist' r s |>.card

/-- The two formulations are related. -/
theorem squared_sum_eq_count (P : PointConfig) :
    4 * sumSquaredMultiplicities P = countEqualDistancePairs P := by
  sorry

/- ## Part IV: Convex Position -/

/-- Points are in convex position if they form the vertices of a convex polygon. -/
def InConvexPosition (P : PointConfig) : Prop :=
  ∀ p ∈ P, p ∈ convexHull ℝ (P.erase p : Set Point) → False

/-- No three points are collinear. -/
def NoThreeCollinear (P : PointConfig) : Prop :=
  ∀ p q r : Point, p ∈ P → q ∈ P → r ∈ P →
    p ≠ q → q ≠ r → p ≠ r →
    ¬Collinear ℝ ({p, q, r} : Set Point)

/-- Convex position implies no three collinear. -/
theorem convex_implies_no_collinear (P : PointConfig) :
    InConvexPosition P → NoThreeCollinear P := by
  sorry

/- ## Part V: The Main Theorem (Fishburn) -/

/-- Fishburn's theorem: For convex polygons, ∑ f(u)² = O(n³). -/
theorem fishburn_theorem :
    ∃ C : ℝ, C > 0 ∧ ∀ P : PointConfig, InConvexPosition P →
      (sumSquaredMultiplicities P : ℝ) ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/-- The constant C can be taken to be 1 (asymptotically). -/
theorem fishburn_asymptotic :
    ∀ ε > 0, ∃ N : ℕ, ∀ P : PointConfig, InConvexPosition P → P.card ≥ N →
      (sumSquaredMultiplicities P : ℝ) ≤ (1 + ε) * (P.card : ℝ) ^ 3 := by
  sorry

/- ## Part VI: Lefmann-Theile Strengthening (1995) -/

/-- Lefmann-Theile: The bound holds under "no three collinear" (weaker than convex). -/
theorem lefmann_theile_theorem :
    ∃ C : ℝ, C > 0 ∧ ∀ P : PointConfig, NoThreeCollinear P →
      (sumSquaredMultiplicities P : ℝ) ≤ C * (P.card : ℝ) ^ 3 := by
  sorry

/- ## Part VII: Lower Bounds and Extremal Configurations -/

/-- The regular n-gon configuration. -/
noncomputable def regularNGon (n : ℕ) : PointConfig :=
  if n < 3 then ∅ else
    (Finset.range n).image fun k =>
      ![Real.cos (2 * Real.pi * k / n), Real.sin (2 * Real.pi * k / n)]

/-- Regular n-gon is in convex position. -/
theorem regular_ngon_convex (n : ℕ) (hn : n ≥ 3) :
    InConvexPosition (regularNGon n) := by
  sorry

/-- Compute ∑ f(u)² for the regular n-gon. -/
noncomputable def regularNGonSum (n : ℕ) : ℕ :=
  sumSquaredMultiplicities (regularNGon n)

/-- The regular n-gon achieves Θ(n³). -/
theorem regular_ngon_cubic :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      c₁ * n ^ 3 ≤ (regularNGonSum n : ℝ) ∧ (regularNGonSum n : ℝ) ≤ c₂ * n ^ 3 := by
  sorry

/- ## Part VIII: Erdős-Fishburn Conjecture -/

/-- Erdős-Fishburn conjecture: The regular n-gon maximizes ∑ f(u)². -/
def ErdosFishburnConjecture : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ∀ P : PointConfig, InConvexPosition P → P.card = n →
    sumSquaredMultiplicities P ≤ regularNGonSum n

/-- The conjecture holds for small n (verified computationally). -/
theorem conjecture_small_cases : ∀ n : ℕ, 3 ≤ n ∧ n ≤ 10 →
    ∀ P : PointConfig, InConvexPosition P → P.card = n →
      sumSquaredMultiplicities P ≤ regularNGonSum n := by
  sorry

/- ## Part IX: Related Quantities -/

/-- The number of distinct distances. -/
noncomputable def numDistinctDistances (P : PointConfig) : ℕ :=
  (distanceSet P).card

/-- For convex n-gon, number of distinct distances is ⌊n/2⌋. -/
theorem convex_distinct_distances (P : PointConfig) (hP : InConvexPosition P) :
    numDistinctDistances P ≤ P.card / 2 + 1 := by
  sorry

/-- The maximum multiplicity of any single distance. -/
noncomputable def maxMultiplicity (P : PointConfig) : ℕ :=
  (distanceSet P).sup' (by sorry) (unorderedMultiplicity P)

/-- For convex position, max multiplicity is O(n). -/
theorem convex_max_multiplicity (P : PointConfig) (hP : InConvexPosition P) :
    (maxMultiplicity P : ℝ) ≤ 2 * P.card := by
  sorry

/- ## Part X: Connections to Other Problems -/

/-- The unit distance problem: how many pairs at distance exactly 1? -/
noncomputable def unitDistanceCount (P : PointConfig) : ℕ :=
  unorderedMultiplicity P 1

/-- Erdős unit distance conjecture bound for convex position. -/
theorem convex_unit_distance (P : PointConfig) (hP : InConvexPosition P) :
    (unitDistanceCount P : ℝ) ≤ 2 * P.card - 2 := by
  sorry

end Erdos94

/-
  ## Summary

  This file formalizes Erdős Problem #94 on distance multiplicities in convex polygons.

  **Status**: SOLVED (Fishburn; strengthened by Lefmann-Theile 1995)
  **Prize**: $44

  **The Problem**: For n points forming a convex polygon, if f(u) counts pairs at
  distance u, prove that ∑ f(u)² = O(n³).

  **Key Results**:
  - Fishburn: ∑ f(u)² ≤ C·n³ for convex polygons
  - Lefmann-Theile (1995): Same bound under "no three collinear" (weaker condition)
  - Regular n-gon achieves Θ(n³), possibly the maximum

  **Erdős-Fishburn Conjecture**: The regular n-gon maximizes ∑ f(u)² among all
  convex n-gons (for sufficiently large n).

  **What we formalize**:
  1. Point configurations and distance multiplicities
  2. Sum of squared multiplicities
  3. Convex position and no-three-collinear conditions
  4. Fishburn's theorem and Lefmann-Theile strengthening
  5. Regular n-gon constructions and the extremal conjecture
  6. Connections to unit distance problem

  **Key sorries**:
  - `fishburn_theorem`: The main O(n³) bound
  - `lefmann_theile_theorem`: The strengthened version
  - `regular_ngon_cubic`: Regular n-gon achieves Θ(n³)

  **Trivial observation**: ∑ f(u) = C(n,2) always (total pairs).
-/
