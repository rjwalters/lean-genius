/-
  Aristotle targets for Erdős Problem #559
  Routine supporting lemmas for automated proof search.
  See Erdos559Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Beck, Friedman-Pippenger, Rödl-Szemerédi — depend on sizeRamsey def-sorry)
  - Routine supporting facts: degree bounds, edge counting, basic graph properties
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos559Aristotle

open Finset Fintype

/-- A simple graph with a finite vertex type -/
structure FiniteGraph (V : Type*) [Fintype V] where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v
  dec : DecidableRel adj := by infer_instance

/-- The number of edges -/
def edgeCount {V : Type*} [Fintype V] [DecidableEq V] [Preorder V]
    (G : FiniteGraph V) [DecidableRel G.adj] : ℕ :=
  (Finset.univ.filter (fun p : V × V => p.1 < p.2 ∧ G.adj p.1 p.2)).card

/-- The degree of a vertex -/
def degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) [DecidableRel G.adj] (v : V) : ℕ :=
  (Finset.univ.filter (fun u => G.adj v u)).card

/-- The maximum degree -/
def maxDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) [DecidableRel G.adj] : ℕ :=
  Finset.univ.sup (degree G)

-- Routine: The degree of any vertex is at most |V| - 1.
-- A vertex can be adjacent to at most all other vertices.
theorem degree_le_card_sub_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) [DecidableRel G.adj] (v : V) :
    degree G v ≤ Fintype.card V - 1 := by
  sorry

-- Routine: The maximum degree is at most |V| - 1.
-- This follows from the degree bound above.
theorem maxDegree_le_card_sub_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : FiniteGraph V) [DecidableRel G.adj] :
    maxDegree G ≤ Fintype.card V - 1 := by
  sorry

-- Routine: A graph with no vertices has edge count 0.
-- Fin 0 is empty, so the edge filter is empty.
theorem edgeCount_empty [Preorder (Fin 0)] (G : FiniteGraph (Fin 0)) [DecidableRel G.adj] :
    edgeCount G = 0 := by
  sorry

-- Routine: A graph with 1 vertex has edge count 0.
-- The only possible edge would be a self-loop, which is forbidden.
theorem edgeCount_single [Preorder (Fin 1)] (G : FiniteGraph (Fin 1)) [DecidableRel G.adj] :
    edgeCount G = 0 := by
  sorry

-- Routine: Graph adjacency is symmetric.
-- This is part of the FiniteGraph structure definition.
theorem graph_adj_symm {V : Type*} [Fintype V]
    (G : FiniteGraph V) (u v : V) (h : G.adj u v) : G.adj v u :=
  G.symm u v h

end Erdos559Aristotle
