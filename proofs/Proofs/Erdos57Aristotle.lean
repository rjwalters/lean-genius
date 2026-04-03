/-
  Aristotle targets for Erdős Problem #57
  Routine supporting lemmas for automated proof search.
  See Erdos57Problem.lean for the main formalization.

  Criteria for inclusion:
  - bipartite_iff_no_odd_cycles: standard graph theory (Mathlib API)
  - colorable_two_no_odd_cycles: 2-colorability implies no odd cycles
  - oddCycleLengths_subset_cycleLengths: definitional subset
  - oddCycleLengths_empty_of_bipartite: bipartite → no odd cycles (half of iff)
  - NOT liu_montgomery_theorem (axiom — major result)
  - NOT HasInfiniteChromaticNumber results (complex)
-/
import Mathlib

namespace Erdos57Aristotle

open Set BigOperators SimpleGraph

variable {V : Type*}

/-- The set of all cycle lengths in a graph using Mathlib's Walk.IsCycle. -/
def cycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n | ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ p.length = n }

/-- The set of all odd cycle lengths in a graph. -/
def oddCycleLengths (G : SimpleGraph V) : Set ℕ :=
  { n ∈ cycleLengths G | Odd n }

/-- A graph is k-colorable if it admits a proper k-coloring. -/
def IsColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ u v, G.Adj u v → f u ≠ f v

-- Routine: The odd cycle lengths are a subset of all cycle lengths.
-- Follows directly from the definition: oddCycleLengths G = { n ∈ cycleLengths G | Odd n }.
theorem oddCycleLengths_subset_cycleLengths (G : SimpleGraph V) :
    oddCycleLengths G ⊆ cycleLengths G := by
  sorry

-- Routine: The empty graph has no cycles, hence no odd cycles.
-- In the empty graph, no edges exist, so no closed walks of length ≥ 3 exist.
theorem oddCycleLengths_empty_graph :
    oddCycleLengths (⊥ : SimpleGraph V) = ∅ := by
  sorry

-- Routine: If a graph is 2-colorable, it has no odd cycles.
-- A proper 2-coloring f : V → Fin 2 assigns each vertex color 0 or 1.
-- Any closed walk must alternate colors, so every cycle has even length.
theorem colorable_two_no_odd_cycles (G : SimpleGraph V)
    (h : IsColorable G 2) : oddCycleLengths G = ∅ := by
  sorry

-- Routine: A bipartite graph has no odd cycles.
-- IsBipartite means ∃ f : V → Bool, colors alternate on edges.
-- Any closed walk alternates f-values, so cycle length is even.
theorem bipartite_no_odd_cycles (G : SimpleGraph V)
    (h : G.IsBipartite) : oddCycleLengths G = ∅ := by
  sorry

-- Routine: A graph is bipartite iff it has no odd cycles.
-- (←) direction: any 2-coloring witnesses bipartiteness.
-- (→) direction: construct a 2-coloring from the bipartite assumption.
-- This is a classical theorem in graph theory.
theorem bipartite_iff_no_odd_cycles (G : SimpleGraph V) :
    G.IsBipartite ↔ oddCycleLengths G = ∅ := by
  sorry

end Erdos57Aristotle
