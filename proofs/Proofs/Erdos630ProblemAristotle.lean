/-
  Aristotle targets for Erdős Problem #630: List Chromatic Number of Planar Bipartite Graphs
  Supporting lemmas about bipartite graph coloring for automated proof search.
  See Erdos630Problem.lean for the main formalization.

  Criteria for inclusion:
  - No dependencies on sorry definitions (listChromaticNumber, IsPlanar, IsOuterplanar)
  - Routine properties of bipartite graphs and GraphCore.chromaticNumber
  - Clean theorem statements derivable from Mathlib's IsBipartite API
  - No axioms
-/
import Mathlib
import Proofs.GraphCore

namespace Erdos630Aristotle

open SimpleGraph GraphCore

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Bipartite graphs are 2-colorable in the GraphCore (IsKColorable) sense.
    IsBipartite gives a 2-coloring; IsKColorable requires ∃ f : V → Fin 2 proper. -/
theorem bipartite_isKColorable2 (G : SimpleGraph V) (hbip : G.IsBipartite) :
    GraphCore.IsKColorable G 2 := by
  sorry

/-- Bipartite graphs have GraphCore.chromaticNumber ≤ 2.
    Follows from bipartite_isKColorable2 and the definition of chromaticNumber as sInf. -/
theorem bipartite_chi_le_2 (G : SimpleGraph V) (hbip : G.IsBipartite) :
    GraphCore.chromaticNumber G ≤ 2 := by
  sorry

/-- The empty graph (no edges) is 1-colorable. -/
theorem bot_isKColorable1 : GraphCore.IsKColorable (⊥ : SimpleGraph V) 1 := by
  sorry

/-- The empty graph (no edges) has chromaticNumber ≤ 1. -/
theorem bot_chi_le_1 : GraphCore.chromaticNumber (⊥ : SimpleGraph V) ≤ 1 := by
  sorry

/-- For a nonempty vertex type, the empty graph has chromaticNumber = 1. -/
theorem bot_chi_eq_1 [Nonempty V] : GraphCore.chromaticNumber (⊥ : SimpleGraph V) = 1 := by
  sorry

/-- Every bipartite graph has GraphCore.chromaticNumber ≤ 2:
    it requires at most 2 colors since it has a proper 2-coloring. -/
theorem bipartite_chi_bound (G : SimpleGraph V) (hbip : G.IsBipartite) :
    GraphCore.chromaticNumber G ≤ 2 := bipartite_chi_le_2 G hbip

end Erdos630Aristotle
