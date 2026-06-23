/-
Erdős Problem #1066: Independence Number of Unit Distance Graphs

Source: https://erdosproblems.com/1066
Status: OPEN

Statement:
Let G be a graph given by n points in ℝ² where any two distinct points
are at least distance 1 apart, and we draw an edge between two points
if they are distance exactly 1 apart.

Let g(n) be maximal such that any such graph always has an independent
set on at least g(n) vertices. Estimate g(n), or perhaps lim g(n)/n.

Current Bounds:
  (8/31)n ≈ 0.258n ≤ g(n) ≤ 0.3125n = (5/16)n

Key Results:
- Lower: Pollack n/4, Csizmadia 9n/35, Swanepoel 8n/31 (best)
- Upper: Erdős n/3 (conjectured), Chung-Graham 6n/19, Pach-Tóth 5n/16 (best)

Reference: https://erdosproblems.com/1066
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

open Real

namespace Erdos1066

/- ## Part I: Basic Definitions -/

/-- A point in ℝ². -/
abbrev Point2D := EuclideanSpace ℝ (Fin 2)

/-- Euclidean distance in ℝ². -/
noncomputable def dist (p q : Point2D) : ℝ :=
  Real.sqrt (‖p - q‖^2)

/-- A set of n points in ℝ² where any two distinct points are at
    distance at least 1. -/
structure UnitDistancePointSet where
  points : Fin n → Point2D
  min_dist : ∀ i j : Fin n, i ≠ j → dist (points i) (points j) ≥ 1

/-- The graph where vertices are points, and edges connect pairs at
    distance exactly 1. -/
def unitDistanceEdge (P : UnitDistancePointSet) (i j : Fin n) : Prop :=
  i ≠ j ∧ dist (P.points i) (P.points j) = 1

/-- A set of vertices with no edges between them. -/
def IsIndependentSet (P : UnitDistancePointSet) (S : Finset (Fin n)) : Prop :=
  ∀ i j : Fin n, i ∈ S → j ∈ S → i ≠ j →
    dist (P.points i) (P.points j) ≠ 1

/-- The size of the largest independent set. -/
noncomputable def independenceNumber (P : UnitDistancePointSet) : ℕ :=
  Nat.find (⟨n, fun S _ => S.card ≤ n⟩ : ∃ k, ∀ S : Finset (Fin n), IsIndependentSet P S → S.card ≤ k)

/- ## Part II: The Function g(n) -/

/-- g(n): The maximum k such that every unit distance point set on n points
    has an independent set of size at least k. Axiomatized since defining
    the infimum over all point configurations requires measure-theoretic
    machinery. -/
axiom g (n : ℕ) : ℕ

/- ## Part III: Lower Bounds -/

/-- Numerical comparison: n/4 = 0.25 < 9/35 ≈ 0.257 < 8/31 ≈ 0.258 -/
theorem lower_bounds_comparison :
    (1 : ℚ) / 4 < 9 / 35 ∧ 9 / 35 < 8 / 31 := by
  constructor <;> norm_num

/- ## Part IV: Upper Bounds -/

/-- Numerical comparison: 5/16 = 0.3125 < 6/19 ≈ 0.316 < 1/3 ≈ 0.333 -/
theorem upper_bounds_comparison :
    (5 : ℚ) / 16 < 6 / 19 ∧ 6 / 19 < 1 / 3 := by
  constructor <;> norm_num

/- ## Part V: Current Best Bounds -/

/-- (8/31) < (5/16): the lower bound is strictly below the upper bound. -/
theorem current_best_bounds :
    (8 : ℚ) / 31 < 5 / 16 := by norm_num

/-- The gap: 5/16 - 8/31 = 27/496 ≈ 0.054.
    The true value of lim g(n)/n lies somewhere in this interval. -/
theorem bound_gap :
    (5 : ℚ) / 16 - 8 / 31 = 27 / 496 := by norm_num

/- ## Part VI: Higher Dimensions -/

/-- g_d(n): For n points in ℝ^d with minimum distance 1, the minimum number
    of points that always have pairwise distance > 1. Axiomatized since
    defining the infimum requires geometric measure theory. -/
axiom g_d (d n : ℕ) : ℕ

/- ## Part VII: Summary -/

/-- **Summary of Erdős Problem #1066:**
    Combines the verified arithmetic facts:
    1. The lower bound 8/31 is strictly less than the upper bound 5/16
    2. The gap is exactly 27/496
    3. The lower bounds improve: 1/4 < 9/35 < 8/31
    4. The upper bounds improve: 5/16 < 6/19 < 1/3 -/
theorem erdos_1066_summary :
    ((8 : ℚ) / 31 < 5 / 16) ∧
    ((5 : ℚ) / 16 - 8 / 31 = 27 / 496) ∧
    ((1 : ℚ) / 4 < 9 / 35 ∧ 9 / 35 < 8 / 31) ∧
    ((5 : ℚ) / 16 < 6 / 19 ∧ 6 / 19 < 1 / 3) :=
  ⟨current_best_bounds, bound_gap, lower_bounds_comparison, upper_bounds_comparison⟩

end Erdos1066
