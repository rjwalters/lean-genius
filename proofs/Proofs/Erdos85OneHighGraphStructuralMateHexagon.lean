import Proofs.Erdos85MatchingMultiplicityRelabel
import Proofs.Erdos85OneHighGraphStructuralSupport
import Proofs.Erdos85OneHighMateMissHexagonGraph

/-! # Direct mate-sector consumer for the structural graph split -/

namespace Erdos85

noncomputable section

/-- An odd standard-mate edge in the relabeled global multiplicity transports
back to an adjacent root pair and directly forces a mate-miss hexagon. -/
theorem exists_oneHighMateMissHexagon_of_structuralMateSector
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hmate : OneHighOddSupportMateEdgeProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))) :
    Nonempty (OneHighMateMissHexagon G v) := by
  obtain ⟨i, hi⟩ := hmate
  let u := p.branchLabel.symm (oneHighStandardPairLow i)
  let w := p.branchLabel.symm (oneHighStandardPairHigh i)
  have hlabels : p.branchLabel u = oneHighStandardPairLow i ∧
      p.branchLabel w = oneHighStandardPairHigh i := by
    simp [u, w]
  have hmateUW : p.mate u = w := by
    apply p.branchLabel.injective
    rw [p.branch_mate]
    simp only [hlabels.1, hlabels.2]
    fin_cases i <;> rfl
  have huw : G.Adj u.1 w.1 := by
    rw [← hmateUW]
    exact p.mate_adj u
  have hodd : Odd (exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj) (min u w, max u w)) := by
    rw [← exchangedMissPairMultiplicity_equiv
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj) p.branchLabel u w]
    simpa [Function.comp_def, hlabels.1, hlabels.2] using hi.2
  exact exists_oneHighMateMissHexagon_of_oddMultiplicity
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
      u w huw hodd

end

end Erdos85
