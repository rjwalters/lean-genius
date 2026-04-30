/-
  Aristotle targets for Erdős Problem #637
  Routine supporting lemmas for automated proof search.
  See Erdos637Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Bukh-Sudakov, JKLY — cited research results)
  - NOT the open optimality conjecture
  - Routine algebraic/set-theoretic consequences of definitions

  Included targets:
  - regular_one_degree: a k-regular graph has exactly 1 distinct degree
  - numDistinctDegrees_le_card: number of distinct degrees ≤ |V|
  - vertexDegree_lt_card: degree < |V| in a simple graph (no self-loops)
-/
import Mathlib

namespace Erdos637ProblemAristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def vertexDegree (G : SimpleGraph V) (v : V) : ℕ :=
  (G.neighborFinset v).card

noncomputable def distinctDegrees (G : SimpleGraph V) : Finset ℕ :=
  Finset.image (vertexDegree G) Finset.univ

noncomputable def numDistinctDegrees (G : SimpleGraph V) : ℕ :=
  (distinctDegrees G).card

def IsRegular (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ v : V, vertexDegree G v = k

-- Routine: a k-regular graph has exactly 1 distinct degree.
-- All degrees equal k, so the image of vertexDegree over all vertices is {k}.
theorem regular_one_degree (G : SimpleGraph V) (k : ℕ) [Nonempty V] (h : IsRegular G k) :
    numDistinctDegrees G = 1 := by
  sorry

-- Routine: the number of distinct degrees is at most the number of vertices.
-- Since distinctDegrees is an image of Finset.univ, its cardinality ≤ |V|.
theorem numDistinctDegrees_le_card (G : SimpleGraph V) :
    numDistinctDegrees G ≤ Fintype.card V := by
  sorry

-- Routine: in a simple graph, the degree of any vertex is < |V|.
-- A vertex cannot be adjacent to itself, so it has at most |V| - 1 neighbors.
theorem vertexDegree_lt_card (G : SimpleGraph V) (v : V) (hV : Fintype.card V ≥ 1) :
    vertexDegree G v < Fintype.card V := by
  sorry

end Erdos637ProblemAristotle
