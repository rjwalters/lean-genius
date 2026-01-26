/-!
# Erdős Problem #575 — Bipartite Turán Numbers Dominate

Let F be a finite set of finite graphs containing at least one bipartite
graph. Is it true that there exists a bipartite graph G ∈ F such that
  ex(n; G) ≪_F ex(n; F)?

Here ex(n; F) is the maximum number of edges in an n-vertex graph
containing no subgraph isomorphic to any member of F.

## Background

The Turán extremal function ex(n; F) is central to extremal graph theory.
When F is a single non-bipartite graph H, the Erdős–Stone–Simonovits
theorem gives ex(n; H) = (1 − 1/χ(H) + o(1)) · (n choose 2).
When F contains a bipartite graph, ex(n; F) = o(n²), and the question
is which bipartite member "controls" the extremal function.

## Status: OPEN

This is a problem of Erdős and Simonovits (1982). Related to Problem #180.

*Reference:* [erdosproblems.com/575](https://www.erdosproblems.com/575)
-/

import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Basic

open SimpleGraph Finset

/-! ## Core Definitions -/

/-- The Turán extremal number ex(n; H): maximum number of edges in an
n-vertex simple graph containing no subgraph isomorphic to H.
We define this abstractly as a supremum. -/
noncomputable def turanNumber (n : ℕ) (H : SimpleGraph (Fin n) → Prop) : ℕ :=
  sSup { (Finset.univ.filter fun e : Fin n × Fin n => e.1 < e.2 ∧
    ∃ G : SimpleGraph (Fin n), G.Adj e.1 e.2 ∧ H G).card | True }

/-- Simplified: ex(n; F) for a family F of "forbidden patterns."
We use a predicate-based approach for the exclusion condition. -/
noncomputable def exFamily (n : ℕ) (isForbidden : ℕ → Prop) : ℕ :=
  sSup { m : ℕ | ∃ G : SimpleGraph (Fin n),
    (∀ k, isForbidden k → True) ∧ -- placeholder for "G contains no forbidden subgraph"
    m = Finset.card (Finset.univ.filter fun e : Fin n × Fin n =>
      e.1 < e.2 ∧ G.Adj e.1 e.2) }

/-- A graph is bipartite if its vertex set can be 2-colored such that
edges only go between color classes. -/
def IsBipartiteGraph (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ f : Fin n → Bool, ∀ v w, G.Adj v w → f v ≠ f w

/-! ## Main Conjecture -/

/-- **Erdős Problem #575 (Open, Erdős–Simonovits 1982).**
For any finite family F of graphs containing at least one bipartite graph,
there exists a bipartite G ∈ F such that ex(n; G) = O(ex(n; F)).

In other words, the extremal function of the family is dominated
(up to a constant) by the extremal function of some single bipartite
member. -/
axiom erdos_575_conjecture :
  -- For any finite family containing a bipartite graph,
  -- some bipartite member dominates the extremal function.
  -- (Stated abstractly due to the complexity of graph embeddings.)
  True -- Axiomatized: the formal statement requires graph homomorphism machinery

/-! ## Context: Erdős–Stone–Simonovits -/

/-- **Erdős–Stone–Simonovits Theorem.**
For any non-bipartite graph H with chromatic number χ(H) ≥ 3:
  ex(n; H) = (1 − 1/(χ(H)−1) + o(1)) · n²/2.
This determines ex(n; H) asymptotically for non-bipartite H. -/
axiom erdos_stone_simonovits (χ : ℕ) (hχ : 3 ≤ χ) :
  -- The Turán density is (1 - 1/(χ-1))/2 for graphs of chromatic number χ
  True -- The full formalization requires chromatic number and graph density

/-- For bipartite H, ex(n; H) = o(n²) by Kővári–Sós–Turán.
The exact order is typically a fractional power of n. -/
axiom bipartite_subquadratic :
  -- ex(n; K_{s,t}) ≤ c · n^{2-1/s} for the complete bipartite graph K_{s,t}
  True -- Placeholder for Kővári–Sós–Turán

/-! ## Family Extremal Function Properties -/

/-- ex(n; F) ≤ ex(n; G) for any G ∈ F: excluding more graphs can
only reduce the extremal function. -/
axiom exFamily_le_member :
  -- Adding more forbidden graphs reduces the maximum edge count
  True

/-- If F contains a bipartite graph, then ex(n; F) = o(n²):
the family extremal function is subquadratic. -/
axiom family_with_bipartite_subquadratic :
  -- Follows from the Kővári–Sós–Turán bound on the bipartite member
  True

/-- The conjecture implies that for families with a bipartite member,
the asymptotic behavior of ex(n; F) is controlled by a single
bipartite graph in the family. -/
axiom single_graph_controls :
  -- This is the precise content of Erdős Problem #575
  True
