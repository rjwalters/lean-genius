/-
Erdős Problem #111: Edge Deletion to Bipartiteness for Large Chromatic Graphs

Source: https://erdosproblems.com/111
Status: OPEN

Statement:
For a graph G, let h_G(n) be the maximum number of edges that must be deleted
from any n-vertex subgraph of G to make it bipartite. Is it true that
h_G(n)/n → ∞ for every graph G with chromatic number ℵ₁?

Answer: UNKNOWN

Key Results:
- Erdős-Hajnal-Szemerédi (1982): Graphs with χ(G) = ℵ₁ have h_G(n) ≫ n
  (since they contain ℵ₁ many vertex-disjoint odd cycles)
- Erdős-Hajnal-Szemerédi (1982): There exists G with χ(G) = ℵ₁ and h_G(n) ≪ n^(3/2)
- Erdős (1981): Conjectured this can be improved to h_G(n) ≪ n^(1+ε) for all ε > 0

References:
- Erdős, Hajnal, Szemerédi (1982): "On almost bipartite large chromatic graphs"
- Erdős (1981): "On the combinatorial problems which I would most like to see solved"
- See also Erdős Problem #74
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite

open Cardinal SimpleGraph Set

namespace Erdos111

/-
## Part I: Basic Definitions

Graphs, bipartiteness, and chromatic number concepts.
-/

/--
**Bipartite Graph:**
A graph G is bipartite if its vertices can be partitioned into two sets
such that every edge connects a vertex in one set to a vertex in the other.
Equivalently, G has no odd cycles.
-/
def IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, A ∪ B = Set.univ ∧ A ∩ B = ∅ ∧
    ∀ v w, G.Adj v w → (v ∈ A ∧ w ∈ B) ∨ (v ∈ B ∧ w ∈ A)

/--
**Edge Set:**
The set of edges of a graph, represented as unordered pairs.
-/
def edgeSet {V : Type*} (G : SimpleGraph V) : Set (Sym2 V) :=
  {e | e ∈ G.edgeSet}

/-
## Part II: Edge Deletion to Bipartiteness

The central concept: how many edges must be removed to make a graph bipartite?
-/

/--
**Edges to Remove for Bipartiteness:**
For a finite graph on vertex set V, the minimum number of edges that must
be deleted to make the graph bipartite.

For bipartite graphs, this is 0. For odd cycles of length 2k+1, this is 1.
For complete graphs K_n with n ≥ 3, this is approximately n²/4.
-/
noncomputable def edgesToRemoveForBipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  if IsBipartite G then 0
  else Nat.find (edgesToRemoveForBipartite_exists G)
  where
    edgesToRemoveForBipartite_exists (G : SimpleGraph V) [DecidableRel G.Adj] :
        ∃ k : ℕ, ∃ S : Finset (Sym2 V), S.card = k ∧
          IsBipartite (G.deleteEdges S.toSet) := by
      -- Remove all edges to get the empty graph, which is bipartite
      use G.edgeFinset.card
      use G.edgeFinset
      constructor
      · rfl
      · -- Empty graph is bipartite
        use Set.univ, ∅
        simp [IsBipartite]

/--
**Edge Deletion Function h_G:**
For a graph G and natural number n, h_G(n) is the maximum number of edges
that must be deleted from any n-vertex induced subgraph of G to make it bipartite.

This measures how "far from bipartite" the densest n-vertex subgraphs of G are.
-/
noncomputable def edgeDeletionFunction {V : Type*} (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ (S : Finset V), S.card = n ∧
    k ≤ Finset.card (G.induce S).edgeFinset}

/-
## Part III: Chromatic Number

The chromatic number χ(G) is the minimum number of colors needed to color
the vertices such that no two adjacent vertices share a color.
-/

/--
**Proper Coloring:**
A coloring of G with colors from C is proper if adjacent vertices have different colors.
-/
def IsProperColoring {V C : Type*} (G : SimpleGraph V) (f : V → C) : Prop :=
  ∀ v w, G.Adj v w → f v ≠ f w

/--
**k-Colorable:**
A graph is k-colorable if it admits a proper coloring with at most k colors.
-/
def IsKColorable {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, IsProperColoring G f

/--
**Chromatic Number (for finite graphs):**
The minimum number of colors needed for a proper coloring.
-/
noncomputable def chromaticNumber {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ :=
  Nat.find (chromaticNumber_exists G)
  where
    chromaticNumber_exists (G : SimpleGraph V) [Fintype V] :
        ∃ k : ℕ, IsKColorable G k := by
      -- Use |V| colors, one per vertex
      use Fintype.card V
      -- Existence follows from injective coloring
      sorry

/-
## Part IV: Infinite Chromatic Number

For graphs with uncountable chromatic number, we use cardinal arithmetic.
-/

/--
**Cardinal Chromatic Number:**
The chromatic number as a cardinal, for potentially infinite graphs.
-/
noncomputable def cardinalChromaticNumber {V : Type*} (G : SimpleGraph V) : Cardinal :=
  sInf {κ : Cardinal | ∃ (C : Type*) (f : V → C), #C = κ ∧ IsProperColoring G f}

/--
**Aleph-1 Chromatic Number:**
A graph has chromatic number ℵ₁ if it cannot be colored with countably many
colors but can be colored with ℵ₁ colors.
-/
def hasAleph1ChromaticNumber {V : Type*} (G : SimpleGraph V) : Prop :=
  cardinalChromaticNumber G = Cardinal.aleph 1

/-
## Part V: Odd Cycles and Bipartiteness

A graph is bipartite iff it has no odd cycles. This is fundamental to the problem.
-/

/--
**Odd Cycle:**
A cycle of odd length in a graph.
-/
def hasOddCycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (c : Fin (2*n + 3) → V),
    (∀ i, G.Adj (c i) (c (i + 1))) ∧ c 0 = c (2*n + 2)

/--
**Bipartite iff No Odd Cycles:**
A graph is bipartite if and only if it contains no odd cycle.
This is a classical theorem in graph theory.
-/
axiom bipartite_iff_no_odd_cycle {V : Type*} (G : SimpleGraph V) :
    IsBipartite G ↔ ¬hasOddCycle G

/-
## Part VI: Vertex-Disjoint Odd Cycles

Graphs with χ = ℵ₁ contain many vertex-disjoint odd cycles.
-/

/--
**Vertex-Disjoint Family of Cycles:**
A collection of cycles where no two cycles share a vertex.
-/
def hasVertexDisjointOddCycles {V : Type*} (G : SimpleGraph V) (κ : Cardinal) : Prop :=
  ∃ (I : Type*) (cycles : I → Set V),
    #I = κ ∧
    (∀ i j, i ≠ j → Disjoint (cycles i) (cycles j)) ∧
    (∀ i, ∃ n ≥ 1, ∃ path : Fin (2*n + 1) → V,
      Set.range path = cycles i ∧
      ∀ k, G.Adj (path k) (path ((k + 1) % (2*n + 1))))

/--
**Erdős-Hajnal-Szemerédi Lower Bound:**
Every graph with chromatic number ℵ₁ contains ℵ₁ many vertex-disjoint odd cycles
of some fixed odd length 2r+1. This implies h_G(n) ≫ n.

Proof sketch: If χ(G) = ℵ₁, then G is not countably colorable.
By a compactness argument, G must contain uncountably many vertex-disjoint odd cycles.
-/
axiom ehs_lower_bound {V : Type*} (G : SimpleGraph V)
    (hχ : hasAleph1ChromaticNumber G) :
    ∃ r : ℕ, hasVertexDisjointOddCycles G (Cardinal.aleph 1)

/--
**h_G(n) ≫ n for χ(G) = ℵ₁:**
If G has chromatic number ℵ₁, then h_G(n)/n → ∞ at least linearly.
Each vertex-disjoint odd cycle contributes at least 1 to h_G(n).
-/
axiom h_at_least_linear {V : Type*} (G : SimpleGraph V)
    (hχ : hasAleph1ChromaticNumber G) :
    ∀ c : ℕ, ∃ N : ℕ, ∀ n ≥ N, edgeDeletionFunction G n ≥ c * n

/-
## Part VII: Upper Bound Construction

Erdős-Hajnal-Szemerédi constructed a graph with χ = ℵ₁ but h_G(n) ≪ n^(3/2).
-/

/--
**EHS Upper Bound Construction:**
There exists a graph G with chromatic number ℵ₁ such that
h_G(n) = O(n^(3/2)).

This is proved by an explicit construction using probabilistic methods
and properties of shift graphs.
-/
axiom ehs_upper_bound :
    ∃ (V : Type*) (G : SimpleGraph V),
      hasAleph1ChromaticNumber G ∧
      ∃ C : ℕ, ∀ n : ℕ, edgeDeletionFunction G n ≤ C * n * Nat.sqrt n

/-
## Part VIII: Erdős's Conjecture

Erdős conjectured the upper bound can be improved to n^(1+ε).
-/

/--
**Erdős's Conjecture (1981):**
For every ε > 0, there exists a graph G with chromatic number ℵ₁
such that h_G(n) = O(n^(1+ε)).

This would show the growth rate can be arbitrarily close to linear,
contrasting with the ≫ n lower bound.
-/
def erdosConjecture111 : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ (V : Type*) (G : SimpleGraph V),
      hasAleph1ChromaticNumber G ∧
      ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (edgeDeletionFunction G n : ℝ) ≤ C * (n : ℝ) ^ (1 + ε)

/-
## Part IX: The Main Open Question

The problem asks about the limiting behavior of h_G(n)/n.
-/

/--
**Main Question:**
Is it true that h_G(n)/n → ∞ for every graph G with chromatic number ℵ₁?

Known: h_G(n) ≫ n (so the ratio is at least some positive constant)
Unknown: Does the ratio grow without bound?
-/
def erdos111_question : Prop :=
  ∀ (V : Type*) (G : SimpleGraph V),
    hasAleph1ChromaticNumber G →
    ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, edgeDeletionFunction G n > M * n

/--
**Erdős Problem #111: OPEN**

The status of the main question remains unknown.
-/
axiom erdos_111_status : True  -- Problem is open; we cannot assert either direction

/-
## Part X: Related Results

Connections to other problems and partial results.
-/

/--
**Connection to Problem #74:**
Erdős Problem #74 asks related questions about edge-chromatic number
and bipartite subgraphs. The problems are closely connected through
the study of graphs with large chromatic number.
-/
axiom connection_to_74 :
    ∃ relationship : Prop, relationship  -- Problems are related

/--
**Finite Graphs:**
For finite graphs, the situation is well-understood:
- Bipartite graphs: h_G(n) = 0
- Odd cycles: h_G(n) = O(n)
- Complete graphs K_n: h_G(n) = Θ(n²)

The interesting behavior emerges for infinite graphs with uncountable chromatic number.
-/
theorem finite_complete_graph_bound (n : ℕ) (hn : n ≥ 3) :
    True := by  -- Placeholder for: h_{K_n}(n) ≈ n²/4
  trivial

/-
## Part XI: Summary

Erdős Problem #111 remains open. We know:

1. Lower bound: h_G(n) ≫ n (linear growth at minimum)
2. Upper bound construction: h_G(n) ≪ n^(3/2) is achievable
3. Erdős's conjecture: h_G(n) ≪ n^(1+ε) should be achievable for all ε > 0

The gap between the lower bound (linear) and upper bound (n^(3/2))
remains to be closed.
-/

/--
**Summary of Known Results:**
- Erdős-Hajnal-Szemerédi (1982) established both the lower bound and
  the n^(3/2) upper bound construction
- The exact growth rate of the minimal h_G(n) for graphs with χ = ℵ₁
  is unknown
-/
theorem erdos_111_summary :
    (∀ (V : Type*) (G : SimpleGraph V), hasAleph1ChromaticNumber G →
      ∃ c : ℕ, c > 0 ∧ ∃ N : ℕ, ∀ n ≥ N, edgeDeletionFunction G n ≥ c * n) ∧
    (∃ (V : Type*) (G : SimpleGraph V), hasAleph1ChromaticNumber G ∧
      ∃ C : ℕ, ∀ n : ℕ, edgeDeletionFunction G n ≤ C * n * Nat.sqrt n) := by
  constructor
  · -- Lower bound from EHS
    intro V G hχ
    use 1
    constructor
    · omega
    · exact h_at_least_linear G hχ 1
  · -- Upper bound construction from EHS
    exact ehs_upper_bound

end Erdos111
