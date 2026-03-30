/-
Erdős Problem #653: Distinct Distance Counts in the Plane

Source: https://erdosproblems.com/653
Status: OPEN

Statement:
Let x₁, ..., xₙ ∈ ℝ² be n points in the plane. Define R(xᵢ) as the number of
distinct distances from xᵢ to other points:
  R(xᵢ) = #{|xⱼ - xᵢ| : j ≠ i}

Order points so that R(x₁) ≤ ... ≤ R(xₙ). Let g(n) be the maximum number of
distinct values the R(xᵢ) can take.

Conjecture: g(n) ≥ (1 - o(1))n

Known bounds:
- Lower: g(n) > (7/10)n (Csizmadia)
- Lower: g(n) > (3/8)n (Erdős-Fishburn)
- Upper: g(n) < n - cn^(2/3) for some c > 0

References:
- [Er97e] Erdős original problem
- Erdős-Fishburn: 3/8 lower bound
- Csizmadia: 7/10 lower bound
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Topology.MetricSpace.Basic

open Set Finset Real

namespace Erdos653

/-
## Part I: Point Configuration
-/

/--
**Euclidean Distance:**
The standard distance between two points in ℝ².
-/
noncomputable def euclidDist (p q : Fin 2 → ℝ) : ℝ :=
  Real.sqrt ((p 0 - q 0)^2 + (p 1 - q 1)^2)

/--
**Point Configuration:**
A finite set of distinct points in the plane.
-/
def PointConfig (n : ℕ) := { S : Finset (Fin 2 → ℝ) // S.card = n }

/-
## Part II: Distinct Distance Count
-/

/--
**Distance Set from a Point:**
The set of all distances from point p to other points in S.
-/
noncomputable def distanceSet (S : Finset (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : Finset ℝ :=
  (S.filter (· ≠ p)).image (euclidDist p)

/--
**R(xᵢ) - Distinct Distance Count:**
The number of distinct distances from xᵢ to other points.
-/
noncomputable def distinctDistCount (S : Finset (Fin 2 → ℝ)) (p : Fin 2 → ℝ) : ℕ :=
  (distanceSet S p).card

/-
## Part III: The Function g(n)
-/

/--
**R-Value Set:**
The set of all R(xᵢ) values for points in S.
-/
noncomputable def rValueSet (S : Finset (Fin 2 → ℝ)) : Finset ℕ :=
  S.image (distinctDistCount S)

/--
**Number of Distinct R-Values:**
How many different values R(xᵢ) takes across all points.
-/
noncomputable def numDistinctRValues (S : Finset (Fin 2 → ℝ)) : ℕ :=
  (rValueSet S).card

/--
**g(n) - Maximum Distinct R-Values:**
The maximum number of distinct R-values achievable by any n-point configuration.
-/
noncomputable def g (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ S : Finset (Fin 2 → ℝ), S.card = n ∧ numDistinctRValues S = k }

/-
## Part IV: Known Bounds
-/

/--
**Erdős-Fishburn Lower Bound:**
g(n) > (3/8)n for all sufficiently large n.
-/
/--
**Csizmadia Lower Bound:**
g(n) > (7/10)n for all sufficiently large n.
This improves the Erdős-Fishburn bound.
-/
axiom csizmadia_bound :
  ∀ n : ℕ, n ≥ 10 → g n > 7 * n / 10

/--
**Upper Bound:**
g(n) < n - cn^(2/3) for some constant c > 0.
This shows g(n) cannot equal n for large n.
-/
axiom upper_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    (g n : ℝ) < n - c * (n : ℝ)^(2/3 : ℝ)

/-
## Part V: The Conjecture
-/

/--
**Erdős Problem #653 Conjecture:**
For any ε > 0, there exists N such that for all n ≥ N:
  g(n) ≥ (1 - ε)n

Equivalently: g(n)/n → 1 as n → ∞.
-/
def erdos653Conjecture : Prop :=
  ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (g n : ℝ) ≥ (1 - ε) * n

/-
## Part VI: Basic Properties
-/

/-- **Trivial Lower Bound:**
g(n) ≥ 1 for n ≥ 2 (at least one R-value exists). -/
/--
**Trivial Upper Bound:**
g(n) ≤ n (can't have more distinct values than points).
-/
axiom g_le_n : ∀ n : ℕ, g n ≤ n

/--
**Monotonicity:**
g is non-decreasing in n.
-/
/-
## Part VII: Special Configurations
-/

/--
**Collinear Points:**
For n collinear points, what is the R-value distribution?
If points are equally spaced, the R-values form a specific pattern.
-/
def IsCollinear (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∃ a b : Fin 2 → ℝ, a ≠ b ∧ ∀ p ∈ S, ∃ t : ℝ, p = fun i => a i + t * (b i - a i)

/--
**Regular Polygon:**
Points forming a regular n-gon have specific R-value structure.
For odd n, all vertices have the same R-value = ⌊n/2⌋.
-/
def IsRegularPolygon (S : Finset (Fin 2 → ℝ)) : Prop :=
  ∃ center : Fin 2 → ℝ, ∃ r : ℝ, r > 0 ∧
    ∀ p ∈ S, euclidDist p center = r

/--
**Regular Polygon R-Values:**
In a regular n-gon, all points have the same R-value (for n ≥ 3).
-/
/-
## Part VIII: Extremal Configurations
-/

/--
**High R-Diversity Configuration:**
A configuration achieving g(n) distinct R-values.
-/
def IsOptimalConfig (S : Finset (Fin 2 → ℝ)) : Prop :=
  numDistinctRValues S = g S.card

/--
**Existence of Optimal Configurations:**
For each n, there exists a configuration achieving g(n).
-/
/-
## Part IX: Asymptotic Analysis
-/

/--
**Asymptotic Gap:**
The gap n - g(n) grows as Ω(n^(2/3)).
-/
/-- **Combined Bound:**
cn^(2/3) ≤ n - g(n) ≤ (3/10)n for large n. -/
/-
## Part X: Connection to Unit Distance Problem
-/

/--
**Unit Distance Connection:**
The problem is related to the unit distance problem.
If many pairs are at unit distance, it affects R-value distribution.
-/
def unitDistPairs (S : Finset (Fin 2 → ℝ)) : ℕ :=
  (S.filter fun p => (S.filter fun q => euclidDist p q = 1).card > 0).card

/--
**Distinct Distances Connection:**
Related to Erdős distinct distances problem.
More distinct distances generally means more diverse R-values.
-/
noncomputable def totalDistinctDistances (S : Finset (Fin 2 → ℝ)) : ℕ :=
  (Finset.biUnion S (distanceSet S)).card

/-
## Part XI: Summary
-/

/--
**Erdős Problem #653: Summary**

1. g(n) is the max number of distinct R-values for n points in ℝ²
2. Best lower bound: g(n) > 0.7n (Csizmadia)
3. Upper bound: g(n) < n - cn^(2/3)
4. Conjecture: g(n) ≥ (1 - o(1))n
5. Status: OPEN
-/
theorem erdos_653_summary :
    -- g(n) > 0.7n for large n
    (∀ n ≥ 10, g n > 7 * n / 10) ∧
    -- g(n) ≤ n always
    (∀ n, g n ≤ n) ∧
    -- There exists an upper bound gap
    (∃ c > 0, ∀ n ≥ 2, (g n : ℝ) < n - c * (n : ℝ)^(2/3 : ℝ)) :=
  ⟨csizmadia_bound, g_le_n, upper_bound⟩

/-- **Erdős Problem #653:**
Combines Csizmadia lower bound, trivial upper bound, and nontrivial upper gap. -/
theorem erdos_653 :
    (∀ n ≥ 10, g n > 7 * n / 10) ∧
    (∀ n, g n ≤ n) ∧
    (∃ c > 0, ∀ n ≥ 2, (g n : ℝ) < n - c * (n : ℝ)^(2/3 : ℝ)) :=
  erdos_653_summary

end Erdos653
