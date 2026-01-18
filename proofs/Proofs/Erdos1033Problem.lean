/-
Erdős Problem #1033: Triangle Degree Sums in Dense Graphs

Let h(n) be such that every graph on n vertices with > n²/4 edges contains
a triangle whose vertices have degrees summing to at least h(n). Estimate h(n).

**Status**: OPEN
**Conjecture**: h(n) ≥ (2(√3−1)−o(1))n

**Known Bounds** (Erdős-Laskar 1985, Fan 1988):
- Upper: h(n) ≤ 2(√3−1)n ≈ 1.464n
- Lower: h(n) ≥ (21/16)n = 1.3125n (Fan)

Reference: https://erdosproblems.com/1033
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

namespace Erdos1033

/-
## Graph Setup

We work with simple graphs on a finite vertex set.
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Number of vertices. -/
def vertexCount : ℕ := Fintype.card V

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-
## Turán Threshold

The Turán number n²/4 is the maximum edges without a triangle.
-/

/-- The Turán threshold for triangles. -/
noncomputable def turanThreshold (n : ℕ) : ℕ := n^2 / 4

/-- Graph is above Turán threshold: has more than n²/4 edges. -/
def isAboveTuran (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeCount G > turanThreshold (Fintype.card V)

/-- Turán's theorem: graphs above threshold have triangles. -/
axiom turan_has_triangle (G : SimpleGraph V) [DecidableRel G.Adj] :
  isAboveTuran G → ∃ (a b c : V), a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-
## Triangles and Degree Sums

A triangle is a 3-clique. We study the sum of vertex degrees.
-/

/-- A triangle in G: three mutually adjacent vertices. -/
structure Triangle (G : SimpleGraph V) where
  v1 : V
  v2 : V
  v3 : V
  distinct12 : v1 ≠ v2
  distinct23 : v2 ≠ v3
  distinct13 : v1 ≠ v3
  adj12 : G.Adj v1 v2
  adj23 : G.Adj v2 v3
  adj13 : G.Adj v1 v3

/-- Degree of a vertex in a decidable graph. -/
noncomputable def vertexDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  G.degree v

/-- Sum of degrees of the three vertices in a triangle. -/
noncomputable def triangleDegreeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) : ℕ :=
  vertexDegree G T.v1 + vertexDegree G T.v2 + vertexDegree G T.v3

/-- Set of all triangles in G. -/
def triangles (G : SimpleGraph V) : Set (Triangle G) :=
  Set.univ

/-
## The Function h(n)

h(n) is the largest k such that every graph on n vertices with > n²/4 edges
contains a triangle with degree sum ≥ k.
-/

/-- Graph has a triangle with degree sum at least k. -/
def hasDenseTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ T : Triangle G, triangleDegreeSum G T ≥ k

/-- k is a valid lower bound: all dense graphs have such triangles. -/
def isValidLowerBound (n : ℕ) (k : ℕ) : Prop :=
  ∀ (V : Type*) [DecidableEq V] [Fintype V] [DecidableRel (⊤ : SimpleGraph V).Adj],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G → hasDenseTriangle G k

/-- h(n): the maximum guaranteed degree sum. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | isValidLowerBound n k}

/-- h(n) is well-defined: every valid k works. -/
theorem h_spec (n : ℕ) (hn : n ≥ 3) :
    isValidLowerBound n (h n) := by
  sorry

/-
## The Constant 2(√3 - 1)

This appears in both bounds.
-/

/-- The constant 2(√3 - 1) ≈ 1.464. -/
noncomputable def erdosLaskarConstant : ℝ := 2 * (Real.sqrt 3 - 1)

/-- Numerical value: 2(√3 - 1) ≈ 1.464. -/
theorem erdosLaskar_approx : erdosLaskarConstant > 1.46 ∧ erdosLaskarConstant < 1.47 := by
  sorry

/-
## Erdős-Laskar Upper Bound (1985)

h(n) ≤ 2(√3 - 1)n
-/

/-- Upper bound: h(n) ≤ 2(√3-1)n. -/
axiom erdos_laskar_upper (n : ℕ) (hn : n ≥ 3) :
  (h n : ℝ) ≤ erdosLaskarConstant * n

/-- There exists a graph achieving the upper bound. -/
axiom upper_bound_tight : ∃ N : ℕ, ∀ n ≥ N,
  ∃ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n ∧
  ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G ∧
  (∀ T : Triangle G, (triangleDegreeSum G T : ℝ) ≤ erdosLaskarConstant * n + o(1))

/-
## Erdős-Laskar Lower Bound (1985)

h(n) ≥ (1+c)n for some c > 0.
-/

/-- Original lower bound: h(n) ≥ (1+c)n. -/
axiom erdos_laskar_lower : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N,
  (h n : ℝ) ≥ (1 + c) * n

/-- The lower bound beats n (trivial bound). -/
theorem lower_beats_n : ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, h n ≥ n := by
  obtain ⟨c, hc, N, hN⟩ := erdos_laskar_lower
  use c, hc, N
  intro n hn
  have := hN n hn
  sorry

/-
## Fan's Improved Lower Bound (1988)

h(n) ≥ (21/16)n = 1.3125n
-/

/-- Fan's constant 21/16 = 1.3125. -/
def fanConstant : ℚ := 21 / 16

/-- Fan's bound is better than Erdős-Laskar. -/
theorem fan_improves : (fanConstant : ℝ) > 1 := by
  norm_num [fanConstant]

/-- Fan (1988): h(n) ≥ (21/16)n. -/
axiom fan_lower (n : ℕ) (hn : n ≥ 3) :
  (h n : ℝ) ≥ (fanConstant : ℝ) * n

/-- Fan's bound combined with upper bound. -/
theorem current_bounds (n : ℕ) (hn : n ≥ 3) :
    (fanConstant : ℝ) * n ≤ h n ∧ (h n : ℝ) ≤ erdosLaskarConstant * n := by
  constructor
  · exact fan_lower n hn
  · exact erdos_laskar_upper n hn

/-
## The Gap

There's still a gap between 21/16 ≈ 1.3125 and 2(√3-1) ≈ 1.464.
-/

/-- The gap between known bounds. -/
noncomputable def boundGap : ℝ := erdosLaskarConstant - fanConstant

/-- The gap is positive: problem is open. -/
theorem gap_positive : boundGap > 0 := by
  unfold boundGap erdosLaskarConstant fanConstant
  sorry

/-- Numerical gap ≈ 0.15. -/
theorem gap_approx : boundGap > 0.15 ∧ boundGap < 0.16 := by
  sorry

/-
## The Main Conjecture

Is h(n) ≥ (2(√3-1) - o(1))n? This would close the gap.
-/

/-- The conjecture: h(n) achieves the upper bound asymptotically. -/
def erdos_1033_conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
  (h n : ℝ) ≥ (erdosLaskarConstant - ε) * n

/-- Equivalent formulation: h(n) = (2(√3-1) - o(1))n. -/
def h_asymptotic : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
  |(h n : ℝ) / n - erdosLaskarConstant| < ε

/-- The conjecture implies exact asymptotics. -/
theorem conjecture_gives_asymptotic :
    erdos_1033_conjecture → h_asymptotic := by
  sorry

/-
## Degree Sum Properties

Basic properties of degree sums in triangles.
-/

/-- Each vertex in triangle contributes at least 2 to its degree. -/
theorem triangle_min_degree (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    vertexDegree G T.v1 ≥ 2 ∧ vertexDegree G T.v2 ≥ 2 ∧ vertexDegree G T.v3 ≥ 2 := by
  sorry

/-- Triangle degree sum is at least 6. -/
theorem triangle_sum_min (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) :
    triangleDegreeSum G T ≥ 6 := by
  sorry

/-- In dense graphs, average degree is high. -/
theorem dense_average_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : isAboveTuran G) :
    2 * edgeCount G > Fintype.card V * (Fintype.card V - 1) / 2 := by
  sorry

/-
## Maximum Triangle Degree Sum

The maximum over all triangles.
-/

/-- Maximum triangle degree sum in G. -/
noncomputable def maxTriangleDegreeSum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : ∃ T : Triangle G, True) : ℕ :=
  sSup {triangleDegreeSum G T | T : Triangle G}

/-- h(n) equals minimum of maxTriangleDegreeSum over all dense graphs. -/
theorem h_as_min (n : ℕ) (hn : n ≥ 3) :
    h n = sInf {k : ℕ | ∃ (V : Type*) [DecidableEq V] [Fintype V],
      Fintype.card V = n ∧
      ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj], isAboveTuran G ∧
        ∀ T : Triangle G, triangleDegreeSum G T ≤ k} := by
  sorry

/-
## Extremal Graphs

Graphs that minimize maximum triangle degree sum.
-/

/-- An extremal graph achieves h(n). -/
def isExtremal (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Fintype.card V = n ∧
  isAboveTuran G ∧
  ∀ T : Triangle G, triangleDegreeSum G T ≤ h n

/-- Extremal graphs exist. -/
axiom extremal_exists (n : ℕ) (hn : n ≥ 3) :
  ∃ (V : Type*) [DecidableEq V] [Fintype V],
  ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj], isExtremal n G

/-
## Relation to Turán Graph

The complete bipartite graph K_{n/2, n/2} is the Turán graph.
-/

/-- In balanced bipartite graph, no triangles exist. -/
theorem bipartite_no_triangle (n : ℕ) :
    ∀ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n →
    ∀ G : SimpleGraph V, (∃ (A B : Finset V), A ∪ B = univ ∧ A ∩ B = ∅ ∧
      ∀ a ∈ A, ∀ b ∈ B, G.Adj a b ↔ True) →
    ¬∃ T : Triangle G, True := by
  sorry

/-- Adding one edge to Turán creates triangle with specific degrees. -/
theorem turan_plus_one (n : ℕ) (hn : n ≥ 4) :
    ∃ (V : Type*) [DecidableEq V] [Fintype V],
    Fintype.card V = n ∧
    ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
    edgeCount G = turanThreshold n + 1 ∧
    (∃ T : Triangle G, triangleDegreeSum G T ≥ n) := by
  sorry

/-
## Small Cases

Explicit values for small n.
-/

/-- h(3) = 6: unique triangle, each vertex has degree 2. -/
theorem h_three : h 3 = 6 := by
  sorry

/-- h(4): four vertices, need > 4 edges. -/
theorem h_four : h 4 = 7 := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1033 on triangle degree sums.

**Status**: OPEN

**The Question**: Let h(n) = max k such that every graph on n vertices
with > n²/4 edges has a triangle with degree sum ≥ k. Estimate h(n).

**Conjecture**: h(n) ≥ (2(√3-1) - o(1))n ≈ 1.464n

**Known Bounds**:
- Upper: h(n) ≤ 2(√3-1)n (Erdős-Laskar 1985)
- Lower: h(n) ≥ (21/16)n = 1.3125n (Fan 1988)

**Gap**: About 0.15n between upper and lower bounds.

**Key Insight**: Graphs just above Turán threshold must have
triangles with high degree sum, but exact value is unknown.

**References**:
- Erdős-Laskar (1985): Original bounds
- Fan (1988): Improved lower bound to 21/16

**Related Topics**:
- Turán theory
- Triangle-free graphs
- Degree sequences
-/

end Erdos1033
