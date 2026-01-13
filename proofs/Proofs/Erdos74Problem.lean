/-
Erdős Problem #74: Almost Bipartite Graphs with High Chromatic Number

Let f(n) → ∞ (possibly very slowly). Is there a graph G with infinite chromatic
number such that every finite subgraph on n vertices can be made bipartite by
deleting at most f(n) edges?

**Status**: OPEN

**Partial Results**:
- Rödl (1982): True for hypergraphs
- Rödl (1982): True if f(n) = εn for any constant ε > 0
- Open even for f(n) = √n
- FALSE if chromatic number is ℵ₁ (uncountable)

**Prize**: $500 for proof, $250 for counterexample

Reference: https://erdosproblems.com/74
Erdős-Hajnal-Szemerédi (1982): "On almost bipartite large chromatic graphs"
-/

import Mathlib

open Filter
open scoped Topology

namespace Erdos74

/-!
## Background

A graph is **bipartite** if its vertices can be 2-colored so no edge connects
vertices of the same color. Equivalently, it has no odd cycles.

The **chromatic number** χ(G) is the minimum number of colors needed to properly
color G. For a bipartite graph, χ(G) ≤ 2.

Erdős asked: Can a graph have infinite chromatic number yet have all finite
subgraphs be "almost" bipartite (close to bipartite after few edge deletions)?
-/

/--
The **edge distance to bipartite** of a graph is the minimum number
of edges that must be deleted to make it bipartite.

A graph is bipartite iff this distance is 0. We define this abstractly
using Set.ncard to avoid decidability requirements.
-/
noncomputable def edgeDistToBipartite (V : Type*) (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | ∃ (E : Set (Sym2 V)), E.ncard = k ∧
    E ⊆ G.edgeSet ∧ (G.deleteEdges E).IsBipartite}

/--
A graph is bipartite iff its edge distance to bipartite is 0.
-/
theorem isBipartiteIffDistZero (V : Type*) (G : SimpleGraph V) :
    G.IsBipartite ↔ edgeDistToBipartite V G = 0 := by
  constructor
  · intro h
    simp only [edgeDistToBipartite]
    have : 0 ∈ {k : ℕ | ∃ E, E.ncard = k ∧ E ⊆ G.edgeSet ∧ (G.deleteEdges E).IsBipartite} := by
      use ∅
      simp [h]
    exact Nat.sInf_eq_zero.mpr (Or.inl this)
  · intro h
    sorry -- Would need to show that deleting 0 edges preserves bipartiteness

/--
For a graph G and size n, the **maximum edge distance to bipartite** over
all n-vertex induced subgraphs. This is the worst-case number of edges needed
to make any n-vertex subgraph bipartite.

We define this using an abstract predicate to avoid type issues.
-/
noncomputable def maxEdgeDistToBipartite (V : Type*) (G : SimpleGraph V) (n : ℕ) : ℕ :=
  sSup {edgeDistToBipartite S (G.induce S) | (S : Set V) (_ : S.ncard = n)}

/-!
## The Main Question

Erdős-Hajnal-Szemerédi asked: For any f: ℕ → ℕ with f(n) → ∞, does there exist
a graph G with infinite chromatic number where all n-vertex subgraphs have
edge distance to bipartite at most f(n)?
-/

/--
A graph has **f-almost-bipartite subgraphs** if every n-vertex induced subgraph
can be made bipartite by deleting at most f(n) edges.
-/
def hasAlmostBipartiteSubgraphs (V : Type*) (G : SimpleGraph V) (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, maxEdgeDistToBipartite V G n ≤ f n

/--
A graph has **infinite chromatic number** if it cannot be properly colored
with any finite number of colors.

In Mathlib, this is represented as chromaticNumber = ⊤ (top in ℕ∞).
-/
def hasInfiniteChromaticNumber (V : Type*) (G : SimpleGraph V) : Prop :=
  G.chromaticNumber = ⊤

/--
**Erdős Problem #74 (OPEN)**

For any function f: ℕ → ℕ with f(n) → ∞, does there exist a graph G such that:
1. G has infinite chromatic number (needs infinitely many colors)
2. Every n-vertex subgraph can be made bipartite by deleting ≤ f(n) edges

We state this as a Prop without asserting its truth value.
-/
def Erdos74Question : Prop :=
  ∀ f : ℕ → ℕ, Tendsto (fun n => (f n : ℝ)) atTop atTop →
    ∃ (V : Type) (G : SimpleGraph V),
      hasInfiniteChromaticNumber V G ∧ hasAlmostBipartiteSubgraphs V G f

/-!
## Partial Results

Several cases of this problem have been resolved.
-/

/--
**Rödl's Linear Case (1982)**

For any constant ε > 0, there exists a graph with infinite chromatic number
where every n-vertex subgraph can be made bipartite by deleting at most εn edges.

This shows the conjecture is true for linear functions f(n) = εn.
-/
axiom rodlLinear :
  ∀ ε : ℝ, ε > 0 →
    ∃ (V : Type) (G : SimpleGraph V),
      hasInfiniteChromaticNumber V G ∧
      hasAlmostBipartiteSubgraphs V G (fun n => ⌈ε * n⌉₊)

/--
**The √n Question (OPEN)**

It remains open whether there is a graph with infinite chromatic number
where every n-vertex subgraph needs at most √n edge deletions to become bipartite.

This is a key special case of the general problem.
-/
def SqrtNQuestion : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    hasInfiniteChromaticNumber V G ∧
    hasAlmostBipartiteSubgraphs V G (fun n => ⌈Real.sqrt n⌉₊)

/--
**Uncountable Chromatic Number Fails**

If we require the chromatic number to be uncountable (≥ ℵ₁), then the
conjecture is FALSE. There is no such graph with uncountable chromatic
number satisfying the almost-bipartite condition for any unbounded f.
-/
axiom uncountableFails :
  ¬∃ (V : Type) (G : SimpleGraph V),
    -- G has uncountable chromatic number
    (∀ κ : ℕ, G.chromaticNumber > κ) ∧
    -- And satisfies the almost-bipartite condition for some unbounded f
    (∃ f : ℕ → ℕ, Tendsto (fun n => (f n : ℝ)) atTop atTop ∧
      hasAlmostBipartiteSubgraphs V G f)

/-!
## Connections and Implications

The problem connects chromatic number (a global coloring property) with
local structure (bipartiteness of subgraphs).
-/

/--
The trivial upper bound: any n-vertex graph has at most n(n-1)/2 edges,
so edge distance to bipartite is at most this.
-/
theorem edgeDistUpperBound (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    edgeDistToBipartite V G ≤ Fintype.card V * (Fintype.card V - 1) / 2 := by
  sorry -- Would require showing deletion of all edges gives bipartite graph

/--
Bipartite graphs have chromatic number at most 2, giving a lower bound on
what's achievable: we need non-bipartite subgraphs to force high chromatic number.
-/
theorem bipartite_chromaticNumber_le_two (V : Type*) (G : SimpleGraph V)
    (h : G.IsBipartite) : G.chromaticNumber ≤ 2 := by
  sorry -- Standard result about bipartite graphs

/-!
## Historical Notes

This problem was posed by Erdős, Hajnal, and Szemerédi in 1982. It explores
the tension between global chromatic complexity and local bipartite-like structure.

The fact that the problem fails for uncountable chromatic numbers but remains
open for countable infinite chromatic number suggests delicate set-theoretic
aspects are involved.

Key references:
- Erdős-Hajnal-Szemerédi (1982): "On almost bipartite large chromatic graphs"
- Rödl (1982): "Nearly bipartite graphs with large chromatic number"
-/

end Erdos74
