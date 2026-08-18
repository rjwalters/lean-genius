import Proofs.Erdos85OneHighGraphStructuralMateHexagon

/-! # Terminal-facing structural split for the one-high graph -/

namespace Erdos85

noncomputable section

/-- The unconditional global parity split with its mate-edge branch upgraded
to a concrete graph configuration.  The remaining alternatives are precisely
the all-even, three-root-pair turn, and full cross-block sectors. -/
theorem oneHighGraph_structural_sector_capstone
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (p : OneHighRawV2Presentation G hfree v) :
    let m := exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (fun x => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj x))
    (∀ key ∈ exchangedMissPairKeys (Fin 8), Even (m key)) ∨
      Nonempty (OneHighMateMissHexagon G v) ∨
      OneHighOddSupportThreePairTurnProp m ∨
      OneHighOddSupportCrossBlockProp m := by
  dsimp only
  rcases oneHighGraphExchangedMultiplicity_oddSupport_structural
      G hfree hv hneigh hlocal p with hall | hmate | hturn | hcross
  · exact Or.inl hall
  · exact Or.inr (Or.inl
      (exists_oneHighMateMissHexagon_of_structuralMateSector
        G hfree hv p hmate))
  · exact Or.inr (Or.inr (Or.inl hturn))
  · exact Or.inr (Or.inr (Or.inr hcross))

end

end Erdos85
