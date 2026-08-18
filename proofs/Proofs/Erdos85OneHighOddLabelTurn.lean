import Proofs.Erdos85OneHighOddLabelEdgeSource
import Proofs.Erdos85OneHighRootPairDecoder

/-! # Source-pair classification at an odd label-cycle turn -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A concrete source-colored realization of one odd label-support edge. -/
structure OneHighOddLabelEdgeSourceWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {x : V}, x ∈ secondLayer G v → G.degree x = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (a b : {z : V // z ∈ G.neighborSet v}) where
  sourceEdge : OneHighAllMatchedVertices G v
  sourceEdge_mem : sourceEdge ∈ nonconstantMatchingEdgeSources
    (oneHighGlobalInternalMate G hfree v)
    (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj)
  key_eq : exchangedMissPairKey
    (oneHighGlobalInternalMate G hfree v)
    (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj) sourceEdge = (min a b, max a b)
  left_far : a ∈ ((Finset.univ.erase sourceEdge.1).erase
    (rootMate sourceEdge.1))
  right_far : b ∈ ((Finset.univ.erase sourceEdge.1).erase
    (rootMate sourceEdge.1))

theorem exists_oneHighOddLabelEdgeSourceWitness
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
    Nonempty (OneHighOddLabelEdgeSourceWitness G hfree hv hexternal
      houterDegree rootMate hrootAdj a b) := by
  obtain ⟨x, hx, hkey, ha, hb⟩ :=
    exists_sourceColor_of_oneHigh_oddLabelEdge G hfree hv hexternal
      houterDegree rootMate hrootAdj hadj
  exact ⟨⟨x, hx, hkey, ha, hb⟩⟩

/-- At a turn `a-b-c` whose three labels occupy distinct mate-pairs, concrete
sources for the two odd support edges satisfy the exact four-color
trichotomy: their source pairs agree, or one source pair is the opposite
edge's outer endpoint pair. -/
theorem exists_oneHighOddLabelTurn_sourcePair_trichotomy
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
    {a b c : {z : V // z ∈ G.neighborSet v}}
    (hab : oneHighRootPair (branchLabel a) ≠
      oneHighRootPair (branchLabel b))
    (hbc : oneHighRootPair (branchLabel b) ≠
      oneHighRootPair (branchLabel c))
    (hac : oneHighRootPair (branchLabel a) ≠
      oneHighRootPair (branchLabel c))
    (hadjAB : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj))).Adj a b)
    (hadjBC : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv hexternal houterDegree
          rootMate hrootAdj))).Adj b c) :
    ∃ qAB : OneHighOddLabelEdgeSourceWitness G hfree hv hexternal
        houterDegree rootMate hrootAdj a b,
      ∃ qBC : OneHighOddLabelEdgeSourceWitness G hfree hv hexternal
          houterDegree rootMate hrootAdj b c,
        oneHighRootPair (branchLabel qAB.sourceEdge.1) =
            oneHighRootPair (branchLabel qBC.sourceEdge.1) ∨
          oneHighRootPair (branchLabel qAB.sourceEdge.1) =
            oneHighRootPair (branchLabel c) ∨
          oneHighRootPair (branchLabel qBC.sourceEdge.1) =
            oneHighRootPair (branchLabel a) := by
  obtain ⟨qAB⟩ := exists_oneHighOddLabelEdgeSourceWitness G hfree hv
    hexternal houterDegree rootMate hrootAdj hadjAB
  obtain ⟨qBC⟩ := exists_oneHighOddLabelEdgeSourceWitness G hfree hv
    hexternal houterDegree rootMate hrootAdj hadjBC
  refine ⟨qAB, qBC, ?_⟩
  apply oneHigh_sourcePair_turn_trichotomy
    (branchLabel a) (branchLabel b) (branchLabel c)
    (branchLabel qAB.sourceEdge.1) (branchLabel qBC.sourceEdge.1)
    hab hbc hac
  · exact oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
      hbranchMate qAB.sourceEdge.1 a qAB.left_far
  · exact oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
      hbranchMate qAB.sourceEdge.1 b qAB.right_far
  · exact oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
      hbranchMate qBC.sourceEdge.1 b qBC.left_far
  · exact oneHighRootPair_ne_of_branch_mem_far rootMate branchLabel
      hbranchMate qBC.sourceEdge.1 c qBC.right_far

end

end Erdos85
