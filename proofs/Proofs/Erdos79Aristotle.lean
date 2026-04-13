/-
  Aristotle targets for Erdős Problem #79
  Routine supporting lemmas for automated proof search.
  See Erdos79Problem.lean for the main formalization.

  Criteria for inclusion:
  - K4_edge_count: K₄ on Fin 4 has exactly 6 edges, follows by decide/native_decide
  - complete_graph_edge_count: general complete graph edge count formula
  - complete_graph_vertices: Fintype.card (Fin n) = n
  - Excluded: K4_unique_known (type mismatch), minimal_form_antichain (complex Ramsey)
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos79Aristotle

open SimpleGraph Finset

/-- The number of edges in a finite simple graph. -/
def edgeCount (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  G.edgeFinset.card

-- Routine: The complete graph on Fin 4 has exactly 6 edges.
-- K₄ has C(4,2) = 6 undirected edges.
theorem K4_edge_count :
    (completeGraph (Fin 4)).edgeFinset.card = 6 := by
  sorry

-- Routine: The complete graph on Fin 3 has exactly 3 edges.
-- K₃ has C(3,2) = 3 undirected edges.
theorem K3_edge_count :
    (completeGraph (Fin 3)).edgeFinset.card = 3 := by
  sorry

-- Routine: The complete graph on Fin 2 has exactly 1 edge.
-- K₂ has C(2,2) = 1 undirected edge.
theorem K2_edge_count :
    (completeGraph (Fin 2)).edgeFinset.card = 1 := by
  sorry

-- Routine: K₄ has 4 vertices.
-- Fintype.card (Fin 4) = 4.
theorem K4_vertex_count : Fintype.card (Fin 4) = 4 := by
  sorry

-- Routine: K₃ has 3 vertices.
-- Fintype.card (Fin 3) = 3.
theorem K3_vertex_count : Fintype.card (Fin 3) = 3 := by
  sorry

-- Routine: The complete graph on Fin n has n*(n-1)/2 edges.
-- This is Nat.choose n 2.
theorem complete_graph_edge_count (n : ℕ) :
    (completeGraph (Fin n)).edgeFinset.card = n.choose 2 := by
  sorry

-- Routine: C(4,2) = 6.
-- Nat.choose 4 2 = 6.
theorem choose_4_2 : Nat.choose 4 2 = 6 := by
  sorry

-- Routine: C(3,2) = 3.
-- Nat.choose 3 2 = 3.
theorem choose_3_2 : Nat.choose 3 2 = 3 := by
  sorry

end Erdos79Aristotle
