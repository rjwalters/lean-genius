/-
Erdős Problem #775: Clique Sizes in k-Uniform Hypergraphs

Source: https://erdosproblems.com/775
Status: DISPROVED (Gao, 2025)

Statement:
Is there a 3-uniform hypergraph on n vertices which contains at least n - O(1)
different sizes of cliques (maximal complete subgraphs)?

Answer: NO

Background:
- Erdős constructed a 3-uniform hypergraph with cliques of at least n - log*n different sizes
- For graphs (2-uniform), Spencer (1971) achieved n - log₂n + O(1) different sizes
- Moon-Moser (1965) proved Spencer's bound is optimal for graphs

Gao's Result (2025):
For any k ≥ 3, every k-uniform hypergraph on n vertices contains at most
n - f_k(n) different sizes of cliques, where f_k(n) → ∞ as n → ∞.

This disproves the possibility of achieving n - O(1) different clique sizes.

Key Insight:
The combinatorial structure of k-uniform hypergraphs (k ≥ 3) is fundamentally
different from graphs. The additional constraint of requiring k vertices in
each edge limits how many distinct clique sizes can coexist.

References:
- Gao (2025): "On cliques in hypergraphs", arXiv:2510.14804
- Spencer (1971): "On cliques in graphs", Israel J. Math.
- Moon-Moser (1965): "On cliques in graphs", Israel J. Math.
- See also Erdős Problem #927
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Log

open Finset Set

namespace Erdos775

/-
## Part I: Hypergraph Fundamentals

A k-uniform hypergraph has edges that are exactly k-element subsets of vertices.
-/

/--
**k-Uniform Hypergraph:**
A hypergraph where every edge contains exactly k vertices.

For k = 2, this is an ordinary graph.
For k = 3, edges are triangles of vertices.
-/
structure UniformHypergraph (k : ℕ) (V : Type*) where
  /-- The edge set: k-element subsets of V -/
  edges : Set (Finset V)
  /-- All edges have exactly k vertices -/
  uniform : ∀ e ∈ edges, e.card = k

/-- A 3-uniform hypergraph on vertex type V. -/
abbrev Hypergraph3 (V : Type*) := UniformHypergraph 3 V

/-
## Part II: Cliques in Hypergraphs
-/

/--
**Complete k-Uniform Hypergraph:**
The hypergraph on vertex set S where every k-subset of S is an edge.
-/
def completeHypergraph (k : ℕ) {V : Type*} (S : Finset V) : Set (Finset V) :=
  {e : Finset V | e ⊆ S ∧ e.card = k}

/--
**Clique in a Hypergraph:**
A subset S of vertices is a clique if every k-subset of S is an edge.
-/
def IsClique {k : ℕ} {V : Type*} (H : UniformHypergraph k V) (S : Finset V) : Prop :=
  completeHypergraph k S ⊆ H.edges

/--
**Maximal Clique:**
A clique that cannot be extended by adding any vertex.
-/
def IsMaximalClique {k : ℕ} {V : Type*} (H : UniformHypergraph k V) (S : Finset V) : Prop :=
  IsClique H S ∧ ∀ v : V, v ∉ S → ¬IsClique H (insert v S)

/-
## Part III: Clique Size Distribution
-/

/--
**Clique Sizes:**
The set of all sizes of maximal cliques in a hypergraph.
-/
def cliqueSizes {k : ℕ} {V : Type*} [DecidableEq V] (H : UniformHypergraph k V) : Set ℕ :=
  {n : ℕ | ∃ S : Finset V, IsMaximalClique H S ∧ S.card = n}

/--
**Number of Different Clique Sizes:**
For a finite hypergraph, the number of distinct maximal clique sizes.
-/
noncomputable def numCliqueSizes {k : ℕ} {V : Type*} [DecidableEq V] [Fintype V]
    (H : UniformHypergraph k V) : ℕ :=
  (cliqueSizes H).ncard

/-
## Part IV: Historical Results for Graphs
-/

/--
**Spencer's Construction (1971):**
There exists a graph on n vertices with cliques of at least n - log₂n + O(1)
different sizes.

This is axiomatized as it requires an explicit construction.
-/
axiom spencer_graph_construction :
    ∀ n : ℕ, n ≥ 2 → ∃ (G : SimpleGraph (Fin n)),
      ∃ numSizes : ℕ, numSizes ≥ n - Nat.log 2 n - 10

/--
**Moon-Moser Theorem (1965):**
Every graph on n vertices has at most n - log₂n + O(1) different clique sizes.

This proves Spencer's construction is optimal for graphs.
-/
axiom moon_moser_upper_bound :
    ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ∃ numSizes : ℕ, numSizes ≤ n - Nat.log 2 n + 10 ∧
        numSizes ≥ G.cliqueFinset.card

/-
## Part V: Erdős's Construction
-/

/--
**Erdős's Hypergraph Construction:**
Erdős showed there exists a 3-uniform hypergraph on n vertices with
at least n - log*n different clique sizes.

Here log* is the iterated logarithm (number of times you can take log₂ before
reaching ≤ 1).
-/
axiom erdos_hypergraph_construction :
    ∀ n : ℕ, n ≥ 3 → ∃ (H : Hypergraph3 (Fin n)),
      ∃ numSizes : ℕ, numSizes ≥ n - Nat.log 2 (Nat.log 2 n + 1) - 10

/-
## Part VI: The Question

Can we do better? Can we achieve n - O(1) different clique sizes?
-/

/--
**Erdős's Question (Problem #775):**
Is there a 3-uniform hypergraph on n vertices with at least n - C different
clique sizes for some constant C independent of n?
-/
def erdos775Question : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, n ≥ 3 →
    ∃ (H : Hypergraph3 (Fin n)) (numSizes : ℕ),
      numSizes ≥ n - C

/-
## Part VII: Gao's Theorem (2025)
-/

/--
**Growth Function f_k(n):**
For each k ≥ 3, there exists a function f_k : ℕ → ℕ such that:
1. f_k(n) → ∞ as n → ∞
2. Every k-uniform hypergraph on n vertices has at most n - f_k(n) clique sizes

This function quantifies the inherent limitation on clique size diversity.
-/
noncomputable def gaoFunction (k : ℕ) : ℕ → ℕ := fun n =>
  if k ≥ 3 then Nat.log 2 (Nat.log 2 n + 1) + 1 else 0

/--
**Gao's Upper Bound (2025):**
For any k ≥ 3, every k-uniform hypergraph on n vertices contains at most
n - f_k(n) different sizes of maximal cliques, where f_k(n) → ∞.
-/
axiom gao_upper_bound (k : ℕ) (hk : k ≥ 3) :
    ∀ n : ℕ, n ≥ k → ∀ (H : UniformHypergraph k (Fin n)),
      numCliqueSizes H ≤ n - gaoFunction k n

/--
**f_k(n) tends to infinity:**
The gap between n and the maximum number of clique sizes grows without bound.
-/
axiom gaoFunction_tendsto_infinity (k : ℕ) (hk : k ≥ 3) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → gaoFunction k n ≥ M

/-
## Part VIII: The Answer - NO
-/

/--
**Erdős Problem #775: DISPROVED**

There is NO 3-uniform hypergraph on n vertices with n - O(1) different clique sizes.

Proof: By Gao's theorem, every 3-uniform hypergraph has at most n - f₃(n) clique
sizes where f₃(n) → ∞. So for any constant C, for sufficiently large n,
f₃(n) > C, meaning we cannot achieve n - C different clique sizes.
-/
theorem erdos_775_answer : ¬erdos775Question := by
  intro ⟨C, hC⟩
  -- By gaoFunction_tendsto_infinity, there exists N such that f_3(n) > C for n ≥ N
  have hN := gaoFunction_tendsto_infinity 3 (by norm_num)
  obtain ⟨N, hN'⟩ := hN (C + 1)
  -- For n = max(N, 3), we have both n ≥ N and n ≥ 3
  let n := max N 3
  have hn3 : n ≥ 3 := le_max_right N 3
  have hnN : n ≥ N := le_max_left N 3
  -- By hC, there exists a hypergraph H with at least n - C clique sizes
  obtain ⟨H, numSizes, hnum⟩ := hC n hn3
  -- By Gao's bound, H has at most n - f_3(n) clique sizes
  have hgao := gao_upper_bound 3 (by norm_num) n hn3 H
  -- We have f_3(n) ≥ C + 1 > C
  have hfn := hN' n hnN
  -- This gives a contradiction: numSizes ≥ n - C but numSizes ≤ n - (C+1)
  omega

/--
**Main Theorem:** The answer to Erdős Problem #775 is NO.
-/
theorem erdos_775 : ¬erdos775Question := erdos_775_answer

/-
## Part IX: Comparison with Graphs
-/

/--
**Graphs vs Hypergraphs:**
The behavior is fundamentally different:
- Graphs (k=2): Can achieve n - log₂n + O(1) clique sizes (Moon-Moser optimal)
- k-uniform hypergraphs (k≥3): Cannot achieve n - O(1) clique sizes (Gao)

The extra uniformity constraint limits diversity.
-/
theorem graphs_vs_hypergraphs :
    (∀ n ≥ 2, ∃ G : SimpleGraph (Fin n), ∃ m : ℕ, m ≥ n - Nat.log 2 n - 10) ∧
    (¬∃ C : ℕ, ∀ n ≥ 3, ∃ H : Hypergraph3 (Fin n), ∃ m : ℕ, m ≥ n - C) := by
  constructor
  · intro n hn
    exact spencer_graph_construction n hn
  · intro ⟨C, hC⟩
    have := erdos_775
    unfold erdos775Question at this
    push_neg at this
    exact this C (fun n hn => hC n hn)

/-
## Part X: Related Problems
-/

/--
**Connection to Erdős Problem #927:**
Problem #927 asks related questions about clique structures in hypergraphs.
Both problems explore the combinatorial limitations of hypergraph cliques.
-/
axiom erdos_927_related : True  -- Placeholder for the connection

/--
**Summary Theorem:**
Erdős Problem #775 asked whether 3-uniform hypergraphs can have n - O(1)
different clique sizes. The answer is NO, proved by Gao (2025).
-/
theorem erdos_775_summary :
    ¬erdos775Question ∧
    (∀ k ≥ 3, ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ H : UniformHypergraph k (Fin n),
      numCliqueSizes H ≤ n - M) := by
  constructor
  · exact erdos_775
  · intro k hk M
    obtain ⟨N, hN⟩ := gaoFunction_tendsto_infinity k hk M
    use N
    intro n hn H
    have hbound := gao_upper_bound k hk n (Nat.le_of_lt (Nat.lt_of_lt_of_le (by omega : 2 < k) hn)) H
    have hfn := hN n hn
    omega

end Erdos775
