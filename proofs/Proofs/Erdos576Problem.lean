/-
  Erdős Problem #576: Turán Numbers for Hypercube Graphs

  Source: https://erdosproblems.com/576
  Status: OPEN

  Statement:
  Let Q_k be the k-dimensional hypercube graph (so that Q_k has 2^k vertices
  and k·2^(k-1) edges). Determine the behaviour of ex(n; Q_k).

  Background:
  The Turán number ex(n; H) is the maximum number of edges in an n-vertex graph
  that does not contain H as a subgraph. This is one of the central problems in
  extremal graph theory. For the hypercube Q_k, determining this function remains
  one of the most challenging open problems.

  Known Results:
  - Erdős-Simonovits (1970): (1/2 + o(1))n^(3/2) ≤ ex(n; Q_3) ≪ n^(8/5)
  - Originally Erdős conjectured ex(n; Q_3) ≫ n^(5/3) but this was refined
  - Erdős-Simonovits also proved: if G = Q_3 minus one edge, then ex(n; G) ≍ n^(3/2)
  - Sudakov-Tomon (2022): ex(n; Q_k) = o(n^(2 - 1/k))
  - Janzer-Sudakov (2022): ex(n; Q_k) ≪_k n^(2 - 1/(k-1) + 1/((k-1)·2^(k-1)))

  Open Question:
  Is ex(n; Q_3) ≍ n^(8/5)?

  Tags: extremal-graph-theory, hypercube, turan-number
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.Filter.AtTopBot

namespace Erdos576

open SimpleGraph Finset

/-!
## Part 1: Hypercube Graph Definition

The k-dimensional hypercube graph Q_k has vertices {0,1}^k (all binary strings
of length k) and edges connecting vertices that differ in exactly one coordinate.
-/

/-- A vertex of the k-dimensional hypercube: a function from Fin k to Bool -/
def HypercubeVertex (k : ℕ) := Fin k → Bool

/-- The Hamming distance between two hypercube vertices -/
def hammingDistance {k : ℕ} (v w : HypercubeVertex k) : ℕ :=
  (Finset.univ.filter fun i => v i ≠ w i).card

/-- Two vertices are adjacent in the hypercube iff they differ in exactly one coordinate -/
def hypercubeAdj {k : ℕ} (v w : HypercubeVertex k) : Prop :=
  hammingDistance v w = 1

/-- The hypercube adjacency relation is symmetric -/
theorem hypercubeAdj_symm {k : ℕ} (v w : HypercubeVertex k) :
    hypercubeAdj v w ↔ hypercubeAdj w v := by
  unfold hypercubeAdj hammingDistance
  constructor <;> intro h <;> convert h using 2 <;> ext i <;> exact ne_comm

/-- The hypercube adjacency relation is irreflexive -/
theorem hypercubeAdj_irrefl {k : ℕ} (v : HypercubeVertex k) : ¬hypercubeAdj v v := by
  unfold hypercubeAdj hammingDistance
  simp

/-- The k-dimensional hypercube graph -/
def hypercubeGraph (k : ℕ) : SimpleGraph (HypercubeVertex k) where
  Adj := hypercubeAdj
  symm := fun v w => (hypercubeAdj_symm v w).mp
  loopless := hypercubeAdj_irrefl

notation "Q(" k ")" => hypercubeGraph k

/-!
## Part 2: Properties of Hypercube Graphs

The hypercube Q_k has exactly 2^k vertices and k·2^(k-1) edges.
Each vertex has degree k.
-/

/-- The number of vertices in Q_k is 2^k -/
theorem hypercube_vertex_count (k : ℕ) :
    Fintype.card (HypercubeVertex k) = 2^k := by
  unfold HypercubeVertex
  simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]

/-- Each vertex in Q_k has degree k (stated as a property) -/
axiom hypercube_degree (k : ℕ) (v : HypercubeVertex k) :
    (Q(k)).degree v = k

/-- The number of edges in Q_k is k·2^(k-1) -/
axiom hypercube_edge_count (k : ℕ) :
    (Q(k)).edgeFinset.card = k * 2^(k-1)

/-!
## Part 3: Turán Numbers and Extremal Graph Theory

The extremal number ex(n; H) is the maximum number of edges in an H-free
graph on n vertices.
-/

/-- A graph G is H-free if it contains no subgraph isomorphic to H -/
def IsSubgraphFree {V : Type*} [Fintype V] [DecidableEq V]
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj] : Prop :=
  ¬∃ (f : W ↪ V), ∀ x y, H.Adj x y → G.Adj (f x) (f y)

/-- The Turán number ex(n; H): maximum edges in an n-vertex H-free graph -/
noncomputable def turanNumber (n : ℕ) {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] : ℕ :=
  sSup {m : ℕ | ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj], Fintype.card V = n ∧ IsSubgraphFree G H ∧
    G.edgeFinset.card = m}

notation "ex(" n ";" H ")" => turanNumber n H

/-!
## Part 4: Known Bounds for Hypercube Turán Numbers

The main results on ex(n; Q_k) establish asymptotic bounds.
-/

/-- Erdős-Simonovits (1970) lower bound: ex(n; Q_3) ≥ (1/2 + o(1))n^(3/2) -/
axiom erdos_simonovits_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in Filter.atTop,
      (ex(n; Q(3)) : ℝ) ≥ c * (n : ℝ)^(3/2 : ℝ)

/-- Erdős-Simonovits (1970) upper bound: ex(n; Q_3) ≪ n^(8/5) -/
axiom erdos_simonovits_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in Filter.atTop,
      (ex(n; Q(3)) : ℝ) ≤ C * (n : ℝ)^(8/5 : ℝ)

/-- The combined Erdős-Simonovits bounds for Q_3 -/
theorem erdos_simonovits_bounds :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ᶠ n in Filter.atTop,
      c * (n : ℝ)^(3/2 : ℝ) ≤ (ex(n; Q(3)) : ℝ) ∧
      (ex(n; Q(3)) : ℝ) ≤ C * (n : ℝ)^(8/5 : ℝ) := by
  obtain ⟨c, hc_pos, hc_bound⟩ := erdos_simonovits_lower_bound
  obtain ⟨C, hC_pos, hC_bound⟩ := erdos_simonovits_upper_bound
  exact ⟨c, C, hc_pos, hC_pos, Filter.Eventually.and hc_bound hC_bound⟩

/-!
## Part 5: Recent Progress - Sudakov-Tomon and Janzer-Sudakov

Modern results have improved the upper bounds for general k.
-/

/-- Sudakov-Tomon (2022): ex(n; Q_k) = o(n^(2 - 1/k)) -/
axiom sudakov_tomon_bound (k : ℕ) (hk : k ≥ 2) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop,
      (ex(n; Q(k)) : ℝ) ≤ ε * (n : ℝ)^(2 - 1/(k : ℝ))

/-- The exponent in the Janzer-Sudakov bound: 2 - 1/(k-1) + 1/((k-1)·2^(k-1)) -/
noncomputable def janzerSudakovExponent (k : ℕ) : ℝ :=
  2 - 1/((k : ℝ) - 1) + 1/(((k : ℝ) - 1) * 2^(k - 1))

/-- Janzer-Sudakov (2022): ex(n; Q_k) ≪_k n^(janzerSudakovExponent k) -/
axiom janzer_sudakov_bound (k : ℕ) (hk : k ≥ 3) :
    ∃ C : ℝ, C > 0 ∧ ∀ᶠ n in Filter.atTop,
      (ex(n; Q(k)) : ℝ) ≤ C * (n : ℝ)^(janzerSudakovExponent k)

/-- For k = 3, Janzer-Sudakov gives exponent 2 - 1/2 + 1/8 = 13/8 = 1.625 -/
theorem janzer_sudakov_k3_exponent :
    janzerSudakovExponent 3 = 13/8 := by
  unfold janzerSudakovExponent
  norm_num

/-!
## Part 6: The Main Conjecture

Erdős asked whether ex(n; Q_3) ≍ n^(8/5), meaning the upper bound is tight.
This remains open.
-/

/-- The conjectured behavior: ex(n; Q_3) ≍ n^(8/5) -/
def erdos_conjecture_Q3 : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ᶠ n in Filter.atTop,
    c * (n : ℝ)^(8/5 : ℝ) ≤ (ex(n; Q(3)) : ℝ) ∧
    (ex(n; Q(3)) : ℝ) ≤ C * (n : ℝ)^(8/5 : ℝ)

/-- The gap between known bounds: exponent ranges from 3/2 to 8/5 -/
theorem bound_gap : (8 : ℝ)/5 - 3/2 = 1/10 := by norm_num

/-- Even the improved Janzer-Sudakov bound (13/8) exceeds the conjectured 8/5 -/
theorem janzer_sudakov_vs_conjecture :
    janzerSudakovExponent 3 > (8 : ℝ)/5 := by
  unfold janzerSudakovExponent
  norm_num

/-!
## Part 7: Related Results

Erdős-Simonovits also studied Q_3 with a missing edge.
-/

/-- Q_3 minus one edge has ex(n; G) ≍ n^(3/2) -/
axiom erdos_simonovits_minus_edge :
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ᶠ n in Filter.atTop,
    ∃ (G : SimpleGraph (HypercubeVertex 3)) [DecidableRel G.Adj],
    -- G is Q_3 minus one edge
    (∃ e, G = (Q(3)).deleteEdges {e}) ∧
    c * (n : ℝ)^(3/2 : ℝ) ≤ (ex(n; G) : ℝ) ∧
    (ex(n; G) : ℝ) ≤ C * (n : ℝ)^(3/2 : ℝ)

/-!
## Part 8: General Turán Theory Context

The hypercube Turán problem fits into the broader context of determining
ex(n; H) for bipartite graphs H. For non-bipartite H, the Erdős-Stone theorem
gives ex(n; H) = (1 - 1/(χ(H)-1) + o(1))·(n choose 2).
For bipartite H, the problem is much harder.
-/

/-- The hypercube Q_k is bipartite for all k ≥ 1 -/
axiom hypercube_bipartite (k : ℕ) (hk : k ≥ 1) :
    ∃ (A B : Set (HypercubeVertex k)),
      A ∩ B = ∅ ∧ A ∪ B = Set.univ ∧
      ∀ v w, (Q(k)).Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)

/-- For bipartite H, ex(n; H) = o(n²) -/
axiom bipartite_turan_subquadratic {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hbip : ∃ (A B : Set W), A ∩ B = ∅ ∧ A ∪ B = Set.univ ∧
      ∀ v w, H.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)) :
    ∀ ε > 0, ∀ᶠ n in Filter.atTop, (ex(n; H) : ℝ) ≤ ε * (n : ℝ)^2

/-!
## Part 9: The Kővári-Sós-Turán Theorem

A key tool for bipartite Turán problems.
-/

/-- Kővári-Sós-Turán: ex(n; K_{s,t}) ≤ (1/2)(t-1)^(1/s) · n^(2-1/s) + (s-1)n/2 -/
axiom kovari_sos_turan (s t n : ℕ) (hs : s ≥ 1) (ht : t ≥ s) :
    ∃ C : ℝ, C > 0 ∧ (ex(n; completeBipartiteGraph (Fin s) (Fin t)) : ℝ) ≤
      C * (n : ℝ)^(2 - 1/(s : ℝ))

/-- Q_k contains K_{2,2^(k-1)} as a subgraph -/
axiom hypercube_contains_complete_bipartite (k : ℕ) (hk : k ≥ 2) :
    ∃ (f : Fin 2 ⊕ Fin (2^(k-1)) ↪ HypercubeVertex k),
      ∀ i j, (completeBipartiteGraph (Fin 2) (Fin (2^(k-1)))).Adj (Sum.inl i) (Sum.inr j) →
        (Q(k)).Adj (f (Sum.inl i)) (f (Sum.inr j))

/-!
## Part 10: Summary and Main Theorem

The problem of determining ex(n; Q_k) remains one of the major open problems
in extremal graph theory. Despite significant progress, even the case k = 3
is not fully resolved.
-/

/-- Main theorem: Summary of what is known about ex(n; Q_3)
    Lower bound: Ω(n^(3/2))
    Upper bound: O(n^(8/5)) (Erdős-Simonovits), O(n^(13/8)) (Janzer-Sudakov)
    Conjecture: Θ(n^(8/5))
    Status: OPEN -/
theorem erdos_576_summary :
    -- Lower bound exists
    (∃ c : ℝ, c > 0 ∧ ∀ᶠ n in Filter.atTop,
      (ex(n; Q(3)) : ℝ) ≥ c * (n : ℝ)^(3/2 : ℝ)) ∧
    -- Upper bound exists
    (∃ C : ℝ, C > 0 ∧ ∀ᶠ n in Filter.atTop,
      (ex(n; Q(3)) : ℝ) ≤ C * (n : ℝ)^(8/5 : ℝ)) ∧
    -- Gap between bounds
    ((8 : ℝ)/5 - 3/2 = 1/10) := by
  exact ⟨erdos_simonovits_lower_bound, erdos_simonovits_upper_bound, bound_gap⟩

end Erdos576
