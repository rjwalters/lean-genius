/-
  Aristotle targets for Erdős Problem #610 (Clique Transversal Numbers)
  Routine supporting lemmas for automated proof search.
  See Erdos610Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjectures (erdos_gallai_tuza, egt_bound_tight)
  - NOT malformed theorems with sorry in the type position
  - NOT definition sorries (triangleFreeIndependence, cliqueCoverNumber)
  - Routine bounds and consequences that follow from definitions or axioms

  Excluded (too deep or malformed for Aristotle):
  - erdos_gallai_tuza: The main upper bound (deep combinatorics)
  - egt_bound_tight: Near-tightness construction (deep construction)
  - tau_bipartite / tau_chordal / tau_perfect: have sorry in the type position
  - triangleFreeIndependence: definition sorry
  - cliqueCoverNumber: definition sorry
  - tau_clique_cover_relation: depends on definition sorry
-/
import Mathlib
import Proofs.Erdos610Problem

open scoped Classical

open Finset Function SimpleGraph
open Erdos610

-- v4.31 seam: Erdos610Problem.lean now requires `[Nonempty V]` (soundness fix, #38611 —
-- cliqueTransversalNumber is only well-defined for nonempty V); mirror it here so `τ`
-- resolves, and `open Erdos610` so the conjecture/question Props resolve to the parent's
-- definitions instead of being auto-bound as fresh universe-polymorphic variables.
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

namespace Erdos610Aristotle

/-- τ(G) ≤ n: the full vertex set is a clique transversal of size n.
    Strategy: univ_is_transversal shows Finset.univ works, and
    cliqueTransversalNumber is the min over all transversals. -/
theorem tau_le_card (G : SimpleGraph V) : τ G ≤ Fintype.card V := by
  sorry

/-- Complete graph: τ(⊤) = 1.
    Strategy: the unique maximal clique of ⊤ is all vertices; any single vertex
    intersects it, so τ = 1. Since V is Nontrivial, a single vertex exists. -/
theorem tau_complete [Nontrivial V] : τ (⊤ : SimpleGraph V) = 1 := by
  sorry

/-- If ErdosGallaiTuzaConjecture holds, then Question2_LogImprovement follows.
    Strategy: use kim_triangle_free_independence to extract c₁ > 0 such that
    triangleFreeIndependence n ≥ c₁ * sqrt(n * log n), then apply the conjecture. -/
theorem conjecture_implies_question2 :
    ErdosGallaiTuzaConjecture → Question2_LogImprovement := by
  sorry

end Erdos610Aristotle
