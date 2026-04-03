/-
  Aristotle targets for Erdős Problem #610
  Routine supporting lemmas for automated proof search.
  See Erdos610Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (clique transversal bound)
  - Routine combinatorial facts about cliques and independent sets
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos610Aristotle

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A clique in a graph is a set of pairwise adjacent vertices -/
def IsClique (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/-- An independent set has no edges between its vertices -/
def IsIndependentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v

-- Routine: The empty set is vacuously a clique.
theorem clique_empty (G : SimpleGraph V) :
    IsClique G (∅ : Finset V) := by
  sorry

-- Routine: A singleton set is vacuously a clique.
theorem clique_singleton (G : SimpleGraph V) (v : V) :
    IsClique G ({v} : Finset V) := by
  sorry

-- Routine: A subset of a clique is also a clique.
theorem clique_subset (G : SimpleGraph V) (S T : Finset V)
    (hT : IsClique G T) (hST : S ⊆ T) :
    IsClique G S := by
  sorry

-- Routine: The empty set is vacuously an independent set.
theorem indep_empty (G : SimpleGraph V) :
    IsIndependentSet G (∅ : Finset V) := by
  sorry

-- Routine: A subset of an independent set is also an independent set.
theorem indep_subset (G : SimpleGraph V) (S T : Finset V)
    (hT : IsIndependentSet G T) (hST : S ⊆ T) :
    IsIndependentSet G S := by
  sorry

end Erdos610Aristotle
