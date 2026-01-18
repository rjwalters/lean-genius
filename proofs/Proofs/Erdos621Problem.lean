/-
  Erdős Problem #621: Triangle Edge Covers

  Source: https://erdosproblems.com/621
  Status: SOLVED (Norin-Sun 2016)

  Statement:
  Let G be a graph on n vertices. Define:
  - α₁(G) = maximum number of edges containing at most one edge from every triangle
  - τ₁(G) = minimum number of edges containing at least one edge from every triangle
  Is it true that α₁(G) + τ₁(G) ≤ n²/4?

  Solution:
  - Norin-Sun (2016): Proved α₁(G) + τ_B(G) ≤ n²/4 where τ_B is bipartite removal
  - Since τ₁(G) ≤ τ_B(G), the original conjecture follows

  Historical: Erdős-Gallai-Tuza (1996) noted this "is probably quite difficult"

  Tags: graph-theory, triangles, edge-covers
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Erdos621

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Part I: Basic Definitions -/

/-- A triangle in graph G is a set of 3 pairwise adjacent vertices. -/
def IsTriangle (G : SimpleGraph V) [DecidableRel G.Adj] (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- The set of all triangles in G. -/
def triangles (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (V × V × V) :=
  Finset.univ.filter (fun ⟨a, b, c⟩ => IsTriangle G a b c)

/-- An edge set S "hits" a triangle if S contains at least one edge of the triangle. -/
def HitsTriangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) (a b c : V) : Prop :=
  s(a, b) ∈ S ∨ s(b, c) ∈ S ∨ s(a, c) ∈ S

/-- A triangle edge cover: an edge set hitting every triangle. -/
def IsTriangleEdgeCover (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) : Prop :=
  ∀ a b c, IsTriangle G a b c → HitsTriangle G S a b c

/- ## Part II: The τ₁ Function -/

/-- τ₁(G) = minimum size of a triangle edge cover. -/
noncomputable def tau1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.inf' (Finset.univ.filter (fun S : Finset (Sym2 V) =>
    IsTriangleEdgeCover G S ∧ S ⊆ G.edgeFinset))
    (by sorry) -- nonemptiness
    Finset.card

/-- τ₁(G) is achieved by some edge set. -/
theorem tau1_achieved (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset (Sym2 V), IsTriangleEdgeCover G S ∧ S.card = tau1 G := by
  sorry

/- ## Part III: The α₁ Function -/

/-- An edge set S is "triangle-sparse" if it contains at most one edge from each triangle. -/
def IsTriangleSparse (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset (Sym2 V)) : Prop :=
  ∀ a b c, IsTriangle G a b c →
    (s(a, b) ∈ S ∧ s(b, c) ∈ S → False) ∧
    (s(b, c) ∈ S ∧ s(a, c) ∈ S → False) ∧
    (s(a, b) ∈ S ∧ s(a, c) ∈ S → False)

/-- α₁(G) = maximum size of a triangle-sparse edge set. -/
noncomputable def alpha1 (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.sup' (Finset.univ.filter (fun S : Finset (Sym2 V) =>
    IsTriangleSparse G S ∧ S ⊆ G.edgeFinset))
    (by sorry) -- nonemptiness (empty set works)
    Finset.card

/-- α₁(G) is achieved by some edge set. -/
theorem alpha1_achieved (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ S : Finset (Sym2 V), IsTriangleSparse G S ∧ S.card = alpha1 G := by
  sorry

/- ## Part IV: Bipartite Removal -/

/-- τ_B(G) = minimum number of edges to remove to make G bipartite. -/
noncomputable def tauB (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.inf' (Finset.univ.filter (fun S : Finset (Sym2 V) =>
    S ⊆ G.edgeFinset ∧ (G.deleteEdges (fun e => e ∈ S)).IsBipartite))
    (by sorry) -- nonemptiness
    Finset.card

/-- Bipartite graphs are triangle-free. -/
theorem bipartite_triangle_free (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite) (a b c : V) : ¬IsTriangle G a b c := by
  sorry

/-- τ₁(G) ≤ τ_B(G): Making G bipartite also hits all triangles. -/
theorem tau1_le_tauB (G : SimpleGraph V) [DecidableRel G.Adj] :
    tau1 G ≤ tauB G := by
  sorry

/- ## Part V: The Main Conjecture -/

/-- The Erdős-Gallai-Tuza Conjecture: α₁(G) + τ₁(G) ≤ n²/4. -/
def EGTConjecture (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (alpha1 G + tau1 G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4

/-- The stronger Norin-Sun result: α₁(G) + τ_B(G) ≤ n²/4. -/
def NorinSunResult (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (alpha1 G + tauB G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4

/-- Norin-Sun (2016): The stronger inequality holds. -/
theorem norin_sun_2016 (G : SimpleGraph V) [DecidableRel G.Adj] :
    NorinSunResult G := by
  sorry

/-- Main theorem: The EGT conjecture follows from Norin-Sun. -/
theorem egt_conjecture_resolved (G : SimpleGraph V) [DecidableRel G.Adj] :
    EGTConjecture G := by
  sorry

/- ## Part VI: Equality Cases -/

/-- Complete graph K_n achieves equality. -/
theorem complete_achieves_equality (n : ℕ) (hn : n ≥ 3) :
    ∀ (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    G = ⊤ → -- complete graph
    (alpha1 G + tau1 G : ℝ) = (n : ℝ) ^ 2 / 4 := by
  sorry

/-- Complete bipartite graph K_{n/2,n/2} achieves equality. -/
theorem complete_bipartite_equality (n : ℕ) (hn : Even n) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = n ∧
    (alpha1 G + tau1 G : ℝ) = (n : ℝ) ^ 2 / 4 := by
  sorry

/-- K_{m,m} plus one universal vertex achieves equality. -/
theorem kmm_plus_vertex_equality (m : ℕ) (hm : m ≥ 1) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V)
      (G : SimpleGraph V) (_ : DecidableRel G.Adj),
    Fintype.card V = 2 * m + 1 ∧
    (alpha1 G + tau1 G : ℝ) = ((2 * m + 1 : ℕ) : ℝ) ^ 2 / 4 := by
  sorry

/- ## Part VII: Triangle-Free Graphs -/

/-- For triangle-free graphs, τ₁(G) = 0. -/
theorem triangle_free_tau1_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (htf : ∀ a b c, ¬IsTriangle G a b c) : tau1 G = 0 := by
  sorry

/-- For triangle-free graphs, α₁(G) = |E(G)|. -/
theorem triangle_free_alpha1_all_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (htf : ∀ a b c, ¬IsTriangle G a b c) : alpha1 G = G.edgeFinset.card := by
  sorry

/-- Mantel's theorem: Triangle-free graphs have ≤ n²/4 edges. -/
theorem mantel (G : SimpleGraph V) [DecidableRel G.Adj]
    (htf : ∀ a b c, ¬IsTriangle G a b c) :
    (G.edgeFinset.card : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by
  sorry

/-- For triangle-free graphs, the conjecture reduces to Mantel's theorem. -/
theorem triangle_free_egt (G : SimpleGraph V) [DecidableRel G.Adj]
    (htf : ∀ a b c, ¬IsTriangle G a b c) : EGTConjecture G := by
  sorry

/- ## Part VIII: Dense Graphs -/

/-- In the complete graph, every edge is in a triangle. -/
theorem complete_all_edges_in_triangles (n : ℕ) (hn : n ≥ 3) :
    ∀ (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    ∀ e : Sym2 V, e ∈ (⊤ : SimpleGraph V).edgeFinset →
    ∃ c : V, ∃ a b : V, e = s(a, b) ∧ IsTriangle (⊤ : SimpleGraph V) a b c := by
  sorry

/-- In K_n, α₁ = n²/4 (matching in complete bipartite subgraph). -/
theorem complete_alpha1 (n : ℕ) (hn : n ≥ 2) :
    ∀ (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    (alpha1 (⊤ : SimpleGraph V) : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
  sorry

/- ## Part IX: Bounds and Estimates -/

/-- α₁(G) ≤ n²/4 for all graphs (Turán-type bound). -/
theorem alpha1_upper_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (alpha1 G : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 / 4 := by
  sorry

/-- τ₁(G) ≤ |E(G)| (trivially). -/
theorem tau1_upper_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    tau1 G ≤ G.edgeFinset.card := by
  sorry

/-- τ_B(G) ≤ |E(G)|/2 for any graph. -/
theorem tauB_upper_bound (G : SimpleGraph V) [DecidableRel G.Adj] :
    (tauB G : ℝ) ≤ (G.edgeFinset.card : ℝ) / 2 := by
  sorry

/- ## Part X: Relation to Problem #23 -/

/-- Problem #23 conjectures τ_B(n) ≤ n²/25. -/
def Problem23Conjecture : Prop :=
  ∀ n : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
  Fintype.card V = n →
  ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
  (tauB G : ℝ) ≤ (n : ℝ) ^ 2 / 25

/-- If Problem #23 holds, we get a stronger bound on τ₁. -/
theorem problem23_implies_tau1_bound (h23 : Problem23Conjecture) :
    ∀ n : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
    Fintype.card V = n →
    ∀ (G : SimpleGraph V) [DecidableRel G.Adj],
    (tau1 G : ℝ) ≤ (n : ℝ) ^ 2 / 25 := by
  sorry

end Erdos621

/-
  ## Summary

  This file formalizes Erdős Problem #621 on triangle edge covers.

  **Status**: SOLVED (Norin-Sun 2016)

  **The Problem**: For graph G on n vertices, is α₁(G) + τ₁(G) ≤ n²/4?
  where:
  - α₁(G) = max edges containing ≤ 1 edge from each triangle
  - τ₁(G) = min edges hitting every triangle

  **Answer**: YES! Norin-Sun proved the stronger α₁(G) + τ_B(G) ≤ n²/4.

  **What we formalize**:
  1. Triangle definitions
  2. Triangle edge covers (τ₁)
  3. Triangle-sparse sets (α₁)
  4. Bipartite removal (τ_B)
  5. The main inequality
  6. Equality cases: K_n, K_{n/2,n/2}, K_{m,m}+vertex
  7. Triangle-free special case (Mantel)
  8. Relation to Problem #23

  **Key sorries**:
  - `norin_sun_2016`: The main solved result
  - `egt_conjecture_resolved`: The original conjecture
  - `mantel`: Classical triangle-free bound

  **Historical**: Erdős-Gallai-Tuza (1996) called this "probably quite difficult"
-/
