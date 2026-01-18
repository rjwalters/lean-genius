/-
  Erdős Problem #1009: Edge-Disjoint Triangles Beyond Turán

  Source: https://erdosproblems.com/1009
  Status: SOLVED (Györi 1988)

  Statement:
  Is it true that, for every c > 0, there exists f(c) such that every
  graph on n vertices with at least ⌊n²/4⌋ + k edges, where k < cn,
  contains at least k - f(c) edge-disjoint triangles?

  Background:
  The Turán number ex(n, K₃) = ⌊n²/4⌋ is the maximum edges in a
  triangle-free graph. Once we exceed this threshold, triangles must
  appear. This problem asks: if we exceed by k edges, can we find
  nearly k edge-disjoint triangles?

  History:
  • Erdős (1971) posed this problem
  • Erdős proved f(c) = 0 for c < 1/2 using chromatic number arguments
  • Sauer showed f(2) ≥ 1, so f(c) = 0 doesn't hold for all c
  • Györi (1988) proved the conjecture with f(c) ≪ c²

  The bound f(c) ≪ c² is essentially optimal by Sauer's construction.

  References:
  [Er71] Erdős, "Some unsolved problems in graph theory and combinatorics"
  [Gy88] Györi, "On the number of edge disjoint triangles in K₄-free graphs"

  Tags: graph-theory, triangles, edge-disjoint, turan-numbers, solved
-/

import Mathlib

open Finset SimpleGraph

/-
## Graph Basics

The underlying graph structure and edge counting.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of vertices in the graph -/
noncomputable def numVertices (G : SimpleGraph V) : ℕ := Fintype.card V

/-- Number of edges in G -/
noncomputable def numEdges (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/-- The Turán threshold: ⌊n²/4⌋ -/
def turanThreshold (n : ℕ) : ℕ := n^2 / 4

/-
## Triangles

Triangles in graphs and edge-disjointness.
-/

/-- A triangle in G is three mutually adjacent vertices -/
structure Triangle (G : SimpleGraph V) where
  a : V
  b : V
  c : V
  hab : G.Adj a b
  hbc : G.Adj b c
  hac : G.Adj a c
  distinct : a ≠ b ∧ b ≠ c ∧ a ≠ c

/-- The set of edges in a triangle -/
def Triangle.edges {G : SimpleGraph V} (T : Triangle G) : Finset (Sym2 V) :=
  {s(T.a, T.b), s(T.b, T.c), s(T.a, T.c)}

/-- Two triangles are edge-disjoint if they share no edges -/
def edgeDisjoint {G : SimpleGraph V} (T₁ T₂ : Triangle G) : Prop :=
  T₁.edges ∩ T₂.edges = ∅

/-- A family of triangles is pairwise edge-disjoint -/
def pairwiseEdgeDisjoint {G : SimpleGraph V} (F : Finset (Triangle G)) : Prop :=
  ∀ T₁ ∈ F, ∀ T₂ ∈ F, T₁ ≠ T₂ → edgeDisjoint T₁ T₂

/-- Maximum number of edge-disjoint triangles in G -/
noncomputable def maxEdgeDisjointTriangles (G : SimpleGraph V) : ℕ :=
  sSup {k : ℕ | ∃ F : Finset (Triangle G), F.card = k ∧ pairwiseEdgeDisjoint F}

/-
## The Main Problem

Dense graphs contain many edge-disjoint triangles.
-/

/-- Excess edges above Turán threshold -/
noncomputable def excessEdges (G : SimpleGraph V) [DecidableRel G.Adj] : ℤ :=
  (numEdges G : ℤ) - turanThreshold (numVertices G)

/-- The bound function f(c) -/
noncomputable def boundFunction (c : ℝ) : ℕ := sorry

/-- Györi's main theorem: graphs with n²/4 + k edges contain ≥ k - f(c)
    edge-disjoint triangles when k < cn -/
axiom gyori_theorem :
  ∀ c : ℝ, c > 0 → ∃ f : ℕ, ∀ V : Type*, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj,
      let n := numVertices G
      let k := excessEdges G
      (k ≥ 0) → (k < c * n) →
        (maxEdgeDisjointTriangles G : ℤ) ≥ k - f

/-- Györi's bound: f(c) ≪ c² -/
axiom gyori_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ c : ℝ, c > 0 → (boundFunction c : ℝ) ≤ C * c^2

/-
## Erdős's Partial Result

For small c, we can take f(c) = 0.
-/

/-- Erdős's theorem: f(c) = 0 for c < 1/2 -/
axiom erdos_small_c :
  ∀ V : Type*, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj,
      let n := numVertices G
      let k := excessEdges G
      (k ≥ 0) → (2 * k < n) →
        (maxEdgeDisjointTriangles G : ℤ) ≥ k

/-- Refined bound for odd n: f(c) = 0 for c < 2 -/
axiom gyori_odd_n :
  ∀ V : Type*, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj,
      let n := numVertices G
      let k := excessEdges G
      Odd n → (k ≥ 0) → (k < 2 * n) →
        (maxEdgeDisjointTriangles G : ℤ) ≥ k

/-- Refined bound for even n: f(c) = 0 for c < 3/2 -/
axiom gyori_even_n :
  ∀ V : Type*, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj,
      let n := numVertices G
      let k := excessEdges G
      Even n → (k ≥ 0) → (2 * k < 3 * n) →
        (maxEdgeDisjointTriangles G : ℤ) ≥ k

/-
## Sauer's Counterexample

Shows f(c) > 0 is necessary for large c.
-/

/-- Complete tripartite graph K_{a,b,c} -/
def completeTripartite (a b c : ℕ) : SimpleGraph (Fin a ⊕ Fin b ⊕ Fin c) where
  Adj x y := match x, y with
    | Sum.inl _, Sum.inr (Sum.inl _) => True
    | Sum.inl _, Sum.inr (Sum.inr _) => True
    | Sum.inr (Sum.inl _), Sum.inl _ => True
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => True
    | Sum.inr (Sum.inr _), Sum.inl _ => True
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => True
    | _, _ => False
  symm := by intro x y; simp only; cases x <;> cases y <;> simp
  loopless := by intro x; simp only; cases x <;> simp

/-- Sauer's counterexample: K_{1,m,m} shows f(2) ≥ 1 -/
axiom sauer_counterexample :
  ∃ m : ℕ, m > 0 ∧
    let G := completeTripartite 1 m m
    let n := 1 + 2 * m
    let k := 2 * m -- excess edges
    k = 2 * m ∧ (maxEdgeDisjointTriangles G : ℤ) < k

/-
## Corollaries

Connections to other graph theory results.
-/

/-- The Turán graph is the extremal triangle-free graph -/
axiom turan_extremal :
  ∀ V : Type*, ∀ _ : Fintype V, ∀ _ : DecidableEq V,
    ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj,
      (∀ T : Triangle G, False) → numEdges G ≤ turanThreshold (numVertices G)

/-- Every graph exceeding Turán bound contains a triangle -/
theorem exceeds_turan_has_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : numEdges G > turanThreshold (numVertices G)) :
    ∃ T : Triangle G, True := by
  by_contra hno
  push_neg at hno
  have := turan_extremal V _ _ G _
  · omega
  · intro T; exact hno T trivial

#check gyori_theorem
#check erdos_small_c
#check sauer_counterexample
