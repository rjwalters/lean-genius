import Proofs.Erdos85OneHighCyclicSourceTurnRefinement
import Proofs.Erdos85OneHighDistinctTurnSources

/-! # Concrete source witnesses for the three-pair turn sector -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A three-distinct-pair turn on an odd exchanged-key cycle is realized by
two distinct consecutive internal matching edges.  Their source branches
satisfy the exact four-way graph classification. -/
theorem exists_oneHigh_distinctTurn_sourceWitnesses
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s))
    {l : {z : V // z ∈ G.neighborSet v}}
    {c : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj))).Walk l l}
    (hc : c.IsCycle) (i : Fin c.length)
    (hab : oneHighRootPair (branchLabel (c.getVert i.1)) ≠
      oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc i).1)))
    (hbc : oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc i).1)) ≠
      oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)))
    (hac : oneHighRootPair (branchLabel (c.getVert i.1)) ≠
      oneHighRootPair (branchLabel
        (c.getVert (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1))) :
    ∃ source : Fin c.length → OneHighAllMatchedVertices G v,
      (∀ j : Fin c.length,
        source j ∈ nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj) ∧
        exchangedMissPairKey
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
            rootMate hrootAdj) (source j) =
          (min (c.getVert j.1) (c.getVert (j.1 + 1)),
            max (c.getVert j.1) (c.getVert (j.1 + 1))) ∧
        c.getVert j.1 ∈
          ((Finset.univ.erase (source j).1).erase (rootMate (source j).1)) ∧
        c.getVert (j.1 + 1) ∈
          ((Finset.univ.erase (source j).1).erase (rootMate (source j).1))) ∧
      source i ≠ source (oneHighCycleNext c hc i) ∧
      ((source i).1 = (source (oneHighCycleNext c hc i)).1 ∨
       (source i).1 = rootMate (source (oneHighCycleNext c hc i)).1 ∨
       oneHighRootPair (branchLabel (source i).1) =
          oneHighRootPair (branchLabel (c.getVert
            (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)) ∨
       oneHighRootPair
          (branchLabel (source (oneHighCycleNext c hc i)).1) =
          oneHighRootPair (branchLabel (c.getVert i.1))) := by
  obtain ⟨source, hsource⟩ := exists_sourceColoring_of_oneHigh_oddLabelCycle
    G hfree hv hexternal houterDegree rootMate hrootAdj hc
  refine ⟨source, hsource, ?_, ?_⟩
  · apply oneHigh_sourceColoring_cyclic_turn_sources_ne G v hc
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
        rootMate hrootAdj) source (fun j ↦ (hsource j).2.1) i
    · intro heq
      apply hab
      rw [heq]
    · intro heq
      apply hbc
      rw [heq]
    · intro heq
      apply hac
      rw [heq]
  · apply oneHigh_sourceColoring_cyclic_turn_fourWay
      G v rootMate branchLabel hbranchMate hc source
      (fun j ↦ ⟨(hsource j).2.2.1, (hsource j).2.2.2⟩) i hab hbc hac

end

end Erdos85
