/-
Erdős Problem #1034: Triangle Neighbors in Dense Graphs

Let G be a graph on n vertices with > n²/4 edges. Must there exist a triangle T
and t > (1/2 - o(1))n vertices, each joined to at least two vertices of T?

**Status**: DISPROVED (Ma-Tang)
**Answer**: NO - counterexample shows max t ≤ (2 - √(5/2) + o(1))n ≈ 0.4189n

**Bounds on h(n)** (threshold function):
- Lower: h(n) ≥ (1/6 - o(1))n (from book lemma)
- Upper: h(n) ≤ (2 - √(5/2) + o(1))n (Ma-Tang construction)

Reference: https://erdosproblems.com/1034
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Finset

namespace Erdos1034

/-
## Graph Setup

We work with simple graphs on a finite vertex set.
-/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Number of edges in a graph. -/
noncomputable def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The Turán threshold for triangles. -/
noncomputable def turanThreshold (n : ℕ) : ℕ := n^2 / 4

/-- Graph is above Turán threshold. -/
def isAboveTuran (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  edgeCount G > turanThreshold (Fintype.card V)

/-
## Triangles

A triangle is three mutually adjacent vertices.
-/

/-- A triangle in G. -/
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

/-- The set of triangle vertices. -/
def Triangle.vertices (T : Triangle G) : Finset V :=
  {T.v1, T.v2, T.v3}

/-- Triangle has exactly 3 vertices. -/
theorem Triangle.card_vertices (T : Triangle G) : T.vertices.card = 3 := by
  sorry

/-
## Triangle Neighbors

A vertex y is a "good neighbor" of triangle T if y is adjacent to at least
two vertices of T.
-/

/-- Count of triangle vertices adjacent to y. -/
def adjacentToTriangleCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (y : V) : ℕ :=
  (T.vertices.filter (fun v => G.Adj y v)).card

/-- y is adjacent to at least two vertices of T. -/
def isGoodNeighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (y : V) : Prop :=
  adjacentToTriangleCount G T y ≥ 2

/-- y is adjacent to at least two vertices of T (decidable). -/
instance (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) (y : V) :
    Decidable (isGoodNeighbor G T y) :=
  inferInstanceAs (Decidable (_ ≥ 2))

/-- The set of good neighbors of T (excluding T's vertices). -/
def goodNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) : Finset V :=
  (Finset.univ.filter (fun y => isGoodNeighbor G T y ∧ y ∉ T.vertices))

/-- Count of good neighbors. -/
def goodNeighborCount (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) : ℕ :=
  (goodNeighbors G T).card

/-
## The Function h(n)

h(n) is the largest t such that every graph on n vertices with > n²/4 edges
has a triangle with at least t good neighbors.
-/

/-- G has a triangle with at least k good neighbors. -/
def hasTriangleWithNeighbors (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∃ T : Triangle G, goodNeighborCount G T ≥ k

/-- k is a valid lower bound for h(n). -/
def isValidBound (n : ℕ) (k : ℕ) : Prop :=
  ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G → hasTriangleWithNeighbors G k

/-- h(n): the extremal function. -/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {k : ℕ | isValidBound n k}

/-
## The Original Conjecture (DISPROVED)

Erdős-Faudree conjectured t > (1/2 - o(1))n, which is false.
-/

/-- The original (false) conjecture. -/
def erdos_faudree_conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
  ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G →
  ∃ T : Triangle G, (goodNeighborCount G T : ℝ) > (1/2 - ε) * n

/-- The conjecture is false. -/
theorem erdos_faudree_false : ¬erdos_faudree_conjecture := by
  sorry

/-
## Ma-Tang Counterexample

Ma and Tang constructed a graph disproving the conjecture.
-/

/-- The Ma-Tang constant: 2 - √(5/2) ≈ 0.4189. -/
noncomputable def maTangConstant : ℝ := 2 - Real.sqrt (5/2)

/-- Numerical value verification. -/
theorem maTang_approx : maTangConstant > 0.418 ∧ maTangConstant < 0.42 := by
  sorry

/-- Ma-Tang: There exists a counterexample graph. -/
axiom maTang_counterexample : ∃ N : ℕ, ∀ n ≥ N,
  ∃ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n ∧
  ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G ∧
  (∀ T : Triangle G, (goodNeighborCount G T : ℝ) ≤ maTangConstant * n + o(1))

/-- The upper bound on h(n). -/
theorem h_upper_bound : ∃ N : ℕ, ∀ n ≥ N,
    (h n : ℝ) ≤ maTangConstant * n + 1 := by
  sorry

/-
## Lower Bound via Books

A book is a triangle with many common neighbors.
-/

/-- A book: triangle plus vertices adjacent to all three. -/
def isBook (G : SimpleGraph V) [DecidableRel G.Adj] (T : Triangle G) (pages : Finset V) : Prop :=
  ∀ p ∈ pages, G.Adj p T.v1 ∧ G.Adj p T.v2 ∧ G.Adj p T.v3

/-- Book size = number of pages. -/
def bookSize (pages : Finset V) : ℕ := pages.card

/-- Every graph with > n²/4 edges has a book of size n/6. -/
axiom book_lemma : ∃ N : ℕ, ∀ n ≥ N,
  ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G →
  ∃ T : Triangle G, ∃ pages : Finset V,
    isBook G T pages ∧ bookSize pages ≥ n / 6

/-- Book pages are good neighbors (adjacent to all 3 ≥ 2). -/
theorem book_pages_are_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (pages : Finset V) (hBook : isBook G T pages) :
    ∀ p ∈ pages, p ∉ T.vertices → isGoodNeighbor G T p := by
  sorry

/-- Lower bound: h(n) ≥ (1/6 - o(1))n. -/
theorem h_lower_bound : ∃ N : ℕ, ∀ n ≥ N, (h n : ℝ) ≥ n / 6 - 1 := by
  sorry

/-
## The Gap

There's a gap between 1/6 ≈ 0.167 and 2 - √(5/2) ≈ 0.419.
-/

/-- Current bounds on h(n). -/
theorem h_bounds : ∃ N : ℕ, ∀ n ≥ N,
    (n : ℝ) / 6 - 1 ≤ h n ∧ (h n : ℝ) ≤ maTangConstant * n + 1 := by
  sorry

/-- The gap between bounds. -/
noncomputable def boundGap : ℝ := maTangConstant - 1/6

/-- Gap is substantial: about 0.25. -/
theorem gap_value : boundGap > 0.25 ∧ boundGap < 0.26 := by
  sorry

/-
## K₄-free Variant

Ma-Tang also addressed the K₄-free case.
-/

/-- G is K₄-free. -/
def isK4Free (G : SimpleGraph V) : Prop :=
  ¬∃ (a b c d : V), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    G.Adj a b ∧ G.Adj a c ∧ G.Adj a d ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj c d

/-- The K₄-free constant: 2√3 - 3 ≈ 0.464. -/
noncomputable def k4FreeConstant : ℝ := 2 * Real.sqrt 3 - 3

/-- K₄-free constant verification. -/
theorem k4Free_approx : k4FreeConstant > 0.46 ∧ k4FreeConstant < 0.47 := by
  sorry

/-- Ma-Tang K₄-free result. -/
axiom maTang_k4free : ∃ N : ℕ, ∀ n ≥ N,
  ∃ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n ∧
  ∃ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G ∧ isK4Free G ∧
  (∀ T : Triangle G, (goodNeighborCount G T : ℝ) ≤ k4FreeConstant * n + o(1))

/-- K₄-free bound is worse (higher) than general bound. -/
theorem k4free_worse : k4FreeConstant > maTangConstant := by
  sorry

/-
## Comparison with Problem 905

This is a stronger version of Problem 905.
-/

/-- Problem 905 asks about a single vertex adjacent to two triangle vertices. -/
def problem_905_weaker : Prop :=
  ∀ n : ℕ, ∀ (V : Type*) [DecidableEq V] [Fintype V],
  Fintype.card V = n →
  ∀ G : SimpleGraph V, ∀ [DecidableRel G.Adj],
  isAboveTuran G →
  ∃ T : Triangle G, ∃ y : V, y ∉ T.vertices ∧ isGoodNeighbor G T y

/-- Problem 1034 is stronger than 905. -/
theorem stronger_than_905 :
    (∀ n ≥ 3, isValidBound n 1) → problem_905_weaker := by
  sorry

/-
## Maximum Good Neighbor Count

For a specific graph, the maximum over all triangles.
-/

/-- Maximum good neighbor count over all triangles. -/
noncomputable def maxGoodNeighborCount (G : SimpleGraph V) [DecidableRel G.Adj]
    (hT : ∃ T : Triangle G, True) : ℕ :=
  sSup {goodNeighborCount G T | T : Triangle G}

/-- Graphs achieving the Ma-Tang bound. -/
def isMaTangExtremal (n : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Fintype.card V = n ∧
  isAboveTuran G ∧
  ∀ T : Triangle G, (goodNeighborCount G T : ℝ) ≤ maTangConstant * n + 1

/-
## The Resolved Question

The original question is answered: the conjecture is false.
-/

/-- The question: what is the correct threshold? -/
def erdos_1034_question : Prop :=
  ∃ c : ℝ, c > 0 ∧ (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    |(h n : ℝ) / n - c| < ε)

/-- Partial answer: we know the threshold is between 1/6 and 2-√(5/2). -/
theorem erdos_1034_partial : ∃ c₁ c₂ : ℝ,
    c₁ = 1/6 ∧ c₂ = maTangConstant ∧
    (∃ N : ℕ, ∀ n ≥ N, c₁ * n - 1 ≤ h n ∧ (h n : ℝ) ≤ c₂ * n + 1) := by
  sorry

/-- The conjecture is definitively false. -/
theorem erdos_1034_disproved : ¬erdos_faudree_conjecture := erdos_faudree_false

/-
## Good Neighbor Properties

Basic properties of good neighbors.
-/

/-- A vertex in the triangle is trivially a "good neighbor" of itself. -/
theorem triangle_vertex_adjacent (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) : adjacentToTriangleCount G T T.v1 ≥ 2 := by
  sorry

/-- If y is adjacent to all 3, it's definitely a good neighbor. -/
theorem fully_adjacent_is_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (y : V) (h1 : G.Adj y T.v1) (h2 : G.Adj y T.v2) (h3 : G.Adj y T.v3) :
    adjacentToTriangleCount G T y = 3 := by
  sorry

/-- Good neighbors form a superset of book pages. -/
theorem book_subset_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (T : Triangle G) (pages : Finset V) (hBook : isBook G T pages)
    (hDisjoint : Disjoint pages T.vertices) :
    pages ⊆ goodNeighbors G T := by
  sorry

/-
## Summary

This file formalizes Erdős Problem #1034 on triangle neighbors.

**Status**: DISPROVED (Ma-Tang)

**The Question**: Let G have n vertices and > n²/4 edges. Must there exist
a triangle T with > (1/2 - o(1))n vertices each adjacent to ≥ 2 of T's vertices?

**The Answer**: NO

**Counterexample**: Ma-Tang constructed graphs where every triangle has
at most (2 - √(5/2) + o(1))n ≈ 0.4189n good neighbors.

**Known Bounds** on h(n) (the extremal function):
- Lower: h(n) ≥ (1/6 - o(1))n (from book lemma)
- Upper: h(n) ≤ (2 - √(5/2) + o(1))n (Ma-Tang)

**K₄-free variant**: Upper bound is (2√3 - 3 + o(1))n ≈ 0.464n

**Related Problems**:
- Problem 905 (weaker version)
- Problem 1033 (triangle degree sums)

**References**:
- Erdős-Faudree conjecture
- Ma-Tang counterexample construction
-/

end Erdos1034
