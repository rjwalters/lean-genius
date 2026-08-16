import Proofs.Erdos85OneHighExchangedSourceConstraints
import Proofs.Erdos85OddKeyLabelGraph

/-! # Source colors for odd label-support edges

Every edge of the odd exchanged-key graph on root labels is realized by an
actual nonconstant internal matching edge.  Its source branch avoids both
endpoint labels and their root mates.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- An odd label-support edge carries a concrete source-branch color satisfying
the two endpoint far constraints. -/
theorem exists_sourceColor_of_oneHigh_oddLabelEdge
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    {a b : {z : V // z ∈ G.neighborSet v}}
    (hadj : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj))).Adj a b) :
    ∃ x : OneHighAllMatchedVertices G v,
      x ∈ nonconstantMatchingEdgeSources
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj) ∧
      exchangedMissPairKey
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj) x = (min a b, max a b) ∧
      a ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)) ∧
      b ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)) := by
  have hodd : Odd (exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) (min a b, max a b)) := hadj.2
  have hpos : 0 < exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) (min a b, max a b) := by
    rcases hodd with ⟨k, hk⟩
    omega
  obtain ⟨x, hx, hkey, hmin, hmax⟩ :=
    exists_sourceColor_of_oneHigh_exchangedMultiplicity_pos G hfree hv
      hexternal houterDegree rootMate hrootAdj (min a b, max a b) hpos
  refine ⟨x, hx, hkey, ?_⟩
  rcases le_total a b with hab | hba
  · rw [min_eq_left hab] at hmin
    rw [max_eq_right hab] at hmax
    exact ⟨hmin, hmax⟩
  · rw [min_eq_right hba] at hmin
    rw [max_eq_left hba] at hmax
    exact ⟨hmax, hmin⟩

end

end Erdos85
