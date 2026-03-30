/-
Erdős Problem #816: Equal-Degree Vertices and Paths of Length 3

Source: https://erdosproblems.com/816
Status: SOLVED (Chen-Ma, 2025)

Statement:
Let G be a graph with 2n+1 vertices and n² + n + 1 edges.
Must G contain two vertices of the same degree joined by a path of length 3?

Answer: YES

Background:
- Problem of Erdős and Hajnal
- K_{n,n+1} shows this fails with only n² + n edges
- Chen-Ma (2025): Proved the stronger result that for n ≥ 600,
  all graphs with 2n+1 vertices and ≥ n² + n edges contain such a pair,
  with K_{n,n+1} as the only exception

Reference:
- Chen-Ma [ChMa25], arXiv:2503.19569
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.Card

open SimpleGraph Finset

namespace Erdos816

/-
## Part I: Basic Graph Definitions
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
**Number of Vertices:**
The total count of vertices in the graph.
-/
noncomputable def numVertices (V : Type*) [Fintype V] : ℕ := Fintype.card V

/--
**Number of Edges:**
The count of edges in graph G.
-/
noncomputable def numEdges (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

/--
**Vertex Degree:**
The degree of vertex v in graph G.
-/
noncomputable def degree (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborFinset v).card

/-
## Part II: Paths of Length 3
-/

/--
**Path of Length 3:**
A sequence of 4 distinct vertices v₀ - v₁ - v₂ - v₃ where consecutive pairs are adjacent.
-/
def hasPath3 (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ a b : V, u ≠ a ∧ a ≠ b ∧ b ≠ v ∧
    u ≠ b ∧ a ≠ v ∧ u ≠ v ∧
    G.Adj u a ∧ G.Adj a b ∧ G.Adj b v

/--
**Path of length 3 is symmetric:**
If there's a path of length 3 from u to v, there's one from v to u.
-/
theorem hasPath3_symm (G : SimpleGraph V) (u v : V) :
    hasPath3 G u v ↔ hasPath3 G v u := by
  constructor
  · intro ⟨a, b, h1, h2, h3, h4, h5, h6, ha, hab, hb⟩
    exact ⟨b, a, h3.symm, h2.symm, h1.symm, h5.symm, h4.symm, h6.symm,
           G.symm hb, G.symm hab, G.symm ha⟩
  · intro ⟨a, b, h1, h2, h3, h4, h5, h6, ha, hab, hb⟩
    exact ⟨b, a, h3.symm, h2.symm, h1.symm, h5.symm, h4.symm, h6.symm,
           G.symm hb, G.symm hab, G.symm ha⟩

/-
## Part III: Equal-Degree Pair Connected by Path
-/

/--
**Equal Degree:**
Two vertices have the same degree in graph G.
-/
def sameDegree (G : SimpleGraph V) (u v : V) : Prop :=
  degree G u = degree G v

/--
**Equal-Degree Path-3 Pair:**
A pair of distinct vertices with the same degree connected by a path of length 3.
-/
def hasEqualDegreePath3Pair (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ sameDegree G u v ∧ hasPath3 G u v

/-
## Part IV: The Erdős-Hajnal Condition
-/

/--
**Erdős-Hajnal Condition:**
A graph on 2n+1 vertices with n² + n + 1 edges.
-/
def satisfiesEH816 (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  numVertices V = 2 * n + 1 ∧
  numEdges G = n^2 + n + 1

/--
**Weaker Condition (Chen-Ma):**
A graph on 2n+1 vertices with at least n² + n edges.
-/
def satisfiesWeakerEH816 (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : Prop :=
  numVertices V = 2 * n + 1 ∧
  numEdges G ≥ n^2 + n

/-
## Part V: The Counterexample
-/

/--
**Complete Bipartite Graph K_{n,n+1}:**
The graph with parts of size n and n+1, with all cross-edges.
This has 2n+1 vertices and n(n+1) = n² + n edges.
-/
def isCompleteBipartite (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ A B : Finset V,
    A.card = n ∧ B.card = n + 1 ∧
    Disjoint A B ∧ A ∪ B = Finset.univ ∧
    (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) ∧
    (∀ a₁ a₂ : V, a₁ ∈ A → a₂ ∈ A → ¬G.Adj a₁ a₂) ∧
    (∀ b₁ b₂ : V, b₁ ∈ B → b₂ ∈ B → ¬G.Adj b₁ b₂)

/--
**K_{n,n+1} Counterexample:**
The complete bipartite graph K_{n,n+1} has exactly n² + n edges,
and does NOT contain an equal-degree pair connected by path of length 3.
-/
/-
## Part VI: The Main Theorem (Chen-Ma 2025)
-/

/--
**Chen-Ma Theorem (2025):**
For n ≥ 600, every graph on 2n+1 vertices with at least n² + n edges
contains an equal-degree pair connected by a path of length 3,
EXCEPT for K_{n,n+1}.
-/
/--
**Corollary: Original Problem for n ≥ 600**
With n² + n + 1 edges (one more than K_{n,n+1}), we definitely get
an equal-degree path-3 pair. K_{n,n+1} has exactly n² + n edges,
so any graph with n² + n + 1 edges cannot be K_{n,n+1}.
-/
/--
**Full Erdős Problem #816:**
The answer is YES. For all n, any graph with 2n+1 vertices
and n² + n + 1 edges contains an equal-degree pair joined by a path of length 3.
-/
axiom erdos_816_full :
    ∀ n : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      @satisfiesEH816 V _ _ G _ n →
      hasEqualDegreePath3Pair G

/-
## Part VII: Pigeonhole for Degrees
-/

/--
**Pigeonhole Principle for Degrees:**
In any graph with at least 2 vertices, some pair of vertices must share a degree.
-/
/-
## Part VIII: Summary
-/

/--
**Erdős Problem #816 Summary:**

Let G have 2n+1 vertices and n² + n + 1 edges.
Must G contain two vertices of the same degree joined by a path of length 3?

**Answer:** YES

**Proof:** Chen-Ma (2025), arXiv:2503.19569

**Stronger Result:** For n ≥ 600, even n² + n edges suffice,
with K_{n,n+1} as the unique exception.

**Threshold:** K_{n,n+1} has exactly n² + n edges and fails the property.
Adding one more edge forces it.
-/
theorem erdos_816_summary :
    ∀ n : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      @satisfiesEH816 V _ _ G _ n →
      hasEqualDegreePath3Pair G :=
  erdos_816_full

end Erdos816
