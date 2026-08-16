import Proofs.Erdos85MatchingMultiplicityRelabel
import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighOddLabelTurn

/-! # Concrete graph witnesses from the three-pair turn sector -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The relabeled three-pair turn supplied by the structural capstone pulls
back to two genuine odd root-label edges.  Hence it has two concrete internal
matching-edge sources satisfying the exact source-pair trichotomy. -/
theorem exists_oneHighThreePairTurn_sourcePair_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hturn : OneHighOddSupportThreePairTurnProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))) :
    ∃ a b c : {z : V // z ∈ G.neighborSet v},
      oneHighRootPair (p.branchLabel a) ≠ oneHighRootPair (p.branchLabel b) ∧
      oneHighRootPair (p.branchLabel b) ≠ oneHighRootPair (p.branchLabel c) ∧
      oneHighRootPair (p.branchLabel a) ≠ oneHighRootPair (p.branchLabel c) ∧
      ∃ qAB : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
          p.outer_degree p.mate p.mate_adj a b,
        ∃ qBC : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
            p.outer_degree p.mate p.mate_adj b c,
          oneHighRootPair (p.branchLabel qAB.sourceEdge.1) =
              oneHighRootPair (p.branchLabel qBC.sourceEdge.1) ∨
            oneHighRootPair (p.branchLabel qAB.sourceEdge.1) =
              oneHighRootPair (p.branchLabel c) ∨
            oneHighRootPair (p.branchLabel qBC.sourceEdge.1) =
              oneHighRootPair (p.branchLabel a) := by
  obtain ⟨la, lb, lc, hab, hbc, hac, hAB, hBC⟩ := hturn
  let a := p.branchLabel.symm la
  let b := p.branchLabel.symm lb
  let c := p.branchLabel.symm lc
  have hlabels : p.branchLabel a = la ∧ p.branchLabel b = lb ∧
      p.branchLabel c = lc := by simp [a, b, c]
  have hadj (x y : {z : V // z ∈ G.neighborSet v})
      (hxy : (oddExchangedKeyLabelGraph
        (exchangedMissPairMultiplicity
          (oneHighGlobalInternalMate G hfree v)
          (fun z => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj z)))).Adj (p.branchLabel x) (p.branchLabel y)) :
      (oddExchangedKeyLabelGraph
        (exchangedMissPairMultiplicity
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj))).Adj x y := by
    refine ⟨fun h => hxy.1 (congrArg p.branchLabel h), ?_⟩
    rw [← exchangedMissPairMultiplicity_equiv
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj) p.branchLabel x y]
    simpa [Function.comp_def] using hxy.2
  have hAB' := hadj a b (by simpa [hlabels.1, hlabels.2.1] using hAB)
  have hBC' := hadj b c (by simpa [hlabels.2.1, hlabels.2.2] using hBC)
  obtain ⟨qAB, qBC, hsources⟩ :=
    exists_oneHighOddLabelTurn_sourcePair_trichotomy G hfree hv
      p.external_empty p.outer_degree p.mate p.mate_adj p.branchLabel
      p.branch_mate (by simpa [hlabels.1, hlabels.2.1] using hab)
      (by simpa [hlabels.2.1, hlabels.2.2] using hbc)
      (by simpa [hlabels.1, hlabels.2.2] using hac) hAB' hBC'
  exact ⟨a, b, c,
    by simpa [hlabels.1, hlabels.2.1] using hab,
    by simpa [hlabels.2.1, hlabels.2.2] using hbc,
    by simpa [hlabels.1, hlabels.2.2] using hac,
    qAB, qBC, hsources⟩

end

end Erdos85
