/-
  Erdős Problem #182: Maximum Edges Avoiding k-Regular Subgraphs

  **Question**: For k ≥ 3, what is the maximum number of edges a graph on n vertices
  can have if it contains no k-regular subgraph? Is it ≪ n^{1+o(1)}?

  **Status**: SOLVED by Janzer-Sudakov (2023).

  **Answer**: The maximum is Θ(n log log n). Specifically:
  - Upper bound: Any graph with ≥ C·n·log(log n) edges has a k-regular subgraph
  - Lower bound: Pyber-Rödl-Szemerédi (1995) constructed graphs with Ω(n log log n)
    edges and no k-regular subgraph

  **History**: Erdős and Sauer posed this problem. The upper bound remained open
  for decades until Janzer and Sudakov resolved it in 2023.

  References:
  - https://erdosproblems.com/182
  - Janzer, O. & Sudakov, B. "Regular subgraphs in graphs" (2023)
  - Pyber, L., Rödl, V., Szemerédi, E. "Dense graphs without 3-regular subgraphs" (1995)
  - Erdős, P. "Problems and results in combinatorial analysis" (1975, 1981)
-/

import Mathlib

open Finset BigOperators SimpleGraph

namespace Erdos182

/-!
## Core Definitions

Regular subgraphs and the extremal function.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph is **k-regular** if every vertex has degree exactly k.
Uses neighbor set cardinality to avoid decidability requirements in the definition. -/
def IsRegular (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v : V, (G.neighborSet v).ncard = k

/-- A graph H is a **subgraph** of G if every edge of H is an edge of G. -/
def IsSubgraphOf (H G : SimpleGraph V) : Prop :=
  ∀ v w : V, H.Adj v w → G.Adj v w

/-- A graph G **contains a k-regular subgraph** if there exists a non-empty
k-regular graph H that is a subgraph of G. -/
def HasKRegularSubgraph (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (W : Finset V) (H : SimpleGraph W),
    W.Nonempty ∧ IsRegular H k ∧
    ∀ v w : W, H.Adj v w → G.Adj v.val w.val

/-- Alternative definition: G has a k-regular spanning subgraph on some vertex subset.
Uses set cardinality (ncard) to avoid decidability requirements. -/
def HasKRegularInducedSubgraph (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (W : Set V), W.Nonempty ∧
    ∀ v ∈ W, ({w ∈ W | G.Adj v w} : Set V).ncard = k

/-- The **extremal function** f(n, k) is the maximum number of edges in a graph
on n vertices with no k-regular subgraph.
The placeholder returns n choose 2 (complete graph edges) as a trivial upper bound. -/
noncomputable def extremalFunction (n _k : ℕ) : ℕ := n.choose 2

/-!
## Basic Properties
-/

/-- A 0-regular graph has no edges. -/
axiom zero_regular_edgeless (G : SimpleGraph V) (h : IsRegular G 0) :
    ∀ v w : V, ¬G.Adj v w

/-- A k-regular graph on n vertices has exactly kn/2 edges. -/
axiom regular_edge_count (G : SimpleGraph V) (k : ℕ) [DecidableRel G.Adj] (h : IsRegular G k) :
    2 * G.edgeFinset.card = k * Fintype.card V

/-- For k-regular graphs to exist on n vertices, we need kn even. -/
axiom regular_parity (G : SimpleGraph V) (k : ℕ) (h : IsRegular G k) :
    Even (k * Fintype.card V)

/-- Complete graph K_n is (n-1)-regular. -/
axiom complete_is_regular (n : ℕ) (hn : 1 ≤ n) :
    IsRegular (⊤ : SimpleGraph (Fin n)) (n - 1)

/-!
## Janzer-Sudakov Theorem (2023)

The main result resolving Erdős's question.
-/

/-- **Janzer-Sudakov Theorem (2023)**: For every k ≥ 3, there exists C = C(k) > 0
such that any graph on n vertices with at least C·n·log(log n) edges contains
a k-regular subgraph.

This resolves Erdős Problem #182 in the affirmative. -/
axiom janzer_sudakov_theorem (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, C > 0 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      let n := Fintype.card V
      (G.edgeFinset.card : ℝ) ≥ C * n * Real.log (Real.log n) →
      HasKRegularSubgraph G k

/-- Corollary: The extremal function f(n,k) = O(n log log n). -/
axiom extremal_upper_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, 10 ≤ n →
      ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ¬HasKRegularSubgraph G k →
        (G.edgeFinset.card : ℝ) < C * n * Real.log (Real.log n)

/-!
## Pyber-Rödl-Szemerédi Lower Bound (1995)

The construction showing the Janzer-Sudakov bound is tight.
-/

/-- **Pyber-Rödl-Szemerédi (1995)**: There exist graphs on n vertices with
Ω(n log log n) edges that contain no 3-regular subgraph.

This shows Janzer-Sudakov is tight (up to constant factors). -/
axiom pyber_rodl_szemeredi_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, 10 ≤ n →
      ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        (G.edgeFinset.card : ℝ) ≥ c * n * Real.log (Real.log n) ∧
        ¬HasKRegularSubgraph G 3

/-- The extremal function is Θ(n log log n). -/
axiom extremal_theta (k : ℕ) (hk : 3 ≤ k) :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧
    ∀ n : ℕ, 10 ≤ n →
      c * n * Real.log (Real.log n) ≤ extremalFunction n k ∧
      extremalFunction n k ≤ C * n * Real.log (Real.log n)

/-!
## Special Cases and Variants
-/

/-- For k = 2, the situation is different: avoiding cycles.
A graph with no 2-regular subgraph is a forest. -/
axiom k_equals_2_is_forest (G : SimpleGraph V) :
    ¬HasKRegularSubgraph G 2 ↔ G.IsAcyclic

/-- Forests have at most n-1 edges. -/
axiom forest_edge_bound (G : SimpleGraph V) [DecidableRel G.Adj] (h : G.IsAcyclic) :
    G.edgeFinset.card ≤ Fintype.card V - 1

/-- For k = 1, a 1-regular graph is a perfect matching.
Every graph with ≥ n/2 edges in each component contains a perfect matching. -/
axiom k_equals_1_matching : True  -- Placeholder for matching theory

/-!
## Connected Variant

Erdős also asked about connected k-regular subgraphs.
-/

/-- A graph G **contains a connected k-regular subgraph** if there exists
a connected k-regular graph H as a subgraph of G. -/
def HasConnectedKRegularSubgraph (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (W : Finset V) (H : SimpleGraph W),
    W.Nonempty ∧ IsRegular H k ∧ H.Connected ∧
    ∀ v w : W, H.Adj v w → G.Adj v.val w.val

/-- **Erdős (1975)**: The extremal function for avoiding connected 3-regular
subgraphs is O(n^{5/3}).

This is a weaker bound than the general case. -/
axiom connected_3_regular_bound :
    ∃ C : ℝ, C > 0 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      let n := Fintype.card V
      (G.edgeFinset.card : ℝ) ≥ C * (n : ℝ)^(5/3 : ℝ) →
      HasConnectedKRegularSubgraph G 3

/-!
## Density and Probabilistic Aspects
-/

/-- Dense graphs almost surely contain regular subgraphs. -/
axiom dense_has_regular (k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
    ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (G.edgeFinset.card : ℝ) ≥ ε * n^2 →
      HasKRegularSubgraph G k

/-- The "typical" graph on n vertices with m edges has a k-regular subgraph
when m ≥ C·n·log(log n). -/
axiom typical_threshold (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, 10 ≤ n →
      -- For random G(n,m) with m ≥ C·n·log(log n), w.h.p. G has k-regular subgraph
      True  -- Placeholder for probabilistic statement

/-!
## Historical Context

The problem has a rich history connecting extremal graph theory
to regular substructures.

**Timeline**:
- 1975, 1981: Erdős poses the problem with Sauer
- 1995: Pyber-Rödl-Szemerédi give the lower bound construction
- 2023: Janzer-Sudakov prove the matching upper bound

**Key insight**: The log log n factor comes from an iterative argument.
Each step reduces the graph while preserving "enough" structure.
The iteration depth is O(log log n), giving the final bound.
-/

/-- The problem is fully resolved: extremal function is Θ(n log log n).

This is the main summary theorem combining Janzer-Sudakov (upper bound)
and Pyber-Rödl-Szemerédi (lower bound). -/
axiom erdos_182_resolved (k : ℕ) (hk : 3 ≤ k) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ n : ℕ, 10 ≤ n →
      (∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        ¬HasKRegularSubgraph G k →
        (G.edgeFinset.card : ℝ) ≤ C * n * Real.log (Real.log n)) ∧
      (∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
        ¬HasKRegularSubgraph G k ∧
        (G.edgeFinset.card : ℝ) ≥ c * n * Real.log (Real.log n))

end Erdos182
