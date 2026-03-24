/-
  Aristotle targets for Erdős Problem #637
  Routine supporting lemmas for automated proof search.
  See Erdos637Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Bukh-Sudakov, JKLY) or deep Ramsey bounds
  - Known results provable from Mathlib (image cardinality, degree bounds)
  - Clean theorem statements with no definition sorries
  - No axioms

  The main file formalizes: If G is a Ramsey graph (small clique/independence
  numbers), it must contain an induced subgraph with many distinct degrees.
-/
import Mathlib

namespace Erdos637Aristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/- ## Definitions (mirrored from Erdos637Problem.lean) -/

/-- The degree of a vertex in a graph. -/
noncomputable def vertexDegree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  G.degree v

/-- The set of distinct degrees in a graph. -/
noncomputable def distinctDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : Finset ℕ :=
  Finset.image (vertexDegree G) Finset.univ

/-- Number of distinct degrees in G. -/
noncomputable def numDistinctDegrees (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (distinctDegrees G).card

/-- A graph is k-regular if all degrees equal k. -/
def IsRegular (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ v : V, vertexDegree G v = k

/- ## Routine Lemmas -/

-- Regular graphs
/-- Regular graphs have exactly 1 distinct degree. -/
theorem regular_one_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (h : IsRegular G k) [Nonempty V] :
    numDistinctDegrees G = 1 := by sorry

-- Degree bounds
/-- The number of distinct degrees is at most n (number of vertices). -/
theorem numDistinctDegrees_le_card (G : SimpleGraph V) [DecidableRel G.Adj] :
    numDistinctDegrees G ≤ Fintype.card V := by sorry

/-- The number of distinct degrees is at most n (the max possible degree is n-1). -/
theorem numDistinctDegrees_le_card' (G : SimpleGraph V) [DecidableRel G.Adj] :
    numDistinctDegrees G ≤ Fintype.card V := by sorry

/-- Every vertex has degree at most n-1. -/
theorem degree_lt_card (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    vertexDegree G v < Fintype.card V := by sorry

/-- If the graph has at least one vertex, it has at least one distinct degree. -/
theorem numDistinctDegrees_pos (G : SimpleGraph V) [DecidableRel G.Adj] [Nonempty V] :
    numDistinctDegrees G ≥ 1 := by sorry

-- Induced subgraph degrees
/-- An induced subgraph on a vertex set S. -/
def inducedSubgraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S where
  Adj := fun u v => G.Adj u.val v.val
  symm := fun _ _ h => G.symm h
  loopless := fun v => G.loopless v.val

/-- Degrees in an induced subgraph are bounded by degrees in the full graph. -/
theorem induced_degree_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (v : S) [DecidableRel (inducedSubgraph G S).Adj] :
    (inducedSubgraph G S).degree v ≤ G.degree v.val := by sorry

-- The empty graph
/-- The empty graph (no edges) is 0-regular. -/
theorem bot_regular : IsRegular (⊥ : SimpleGraph V) (DecidableRel := Classical.decRel _) 0 := by sorry

/-- The complete graph on n vertices is (n-1)-regular. -/
theorem top_regular [Nonempty V] :
    IsRegular (⊤ : SimpleGraph V) (DecidableRel := Classical.decRel _) (Fintype.card V - 1) := by sorry

end Erdos637Aristotle
