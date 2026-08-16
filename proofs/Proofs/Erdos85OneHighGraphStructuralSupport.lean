import Proofs.Erdos85OneHighGraphStructuralSector

/-! # Odd-support normal form of the structural graph sectors -/

namespace Erdos85

noncomputable section

/-- The graph's global exchanged-miss odd support is unconditionally either
empty on genuine keys, contains a standard mate edge, contains a turn through
three root-pair colors, or contains the complete cross block between two
root-pair colors. -/
theorem oneHighGraphExchangedMultiplicity_oddSupport_structural
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
      OneHighOddSupportMateEdgeProp m ∨
      OneHighOddSupportThreePairTurnProp m ∨
      OneHighOddSupportCrossBlockProp m := by
  dsimp only
  apply oneHighMultiplicityKnownParitySector_oddSupport
  exact oneHighGraphExchangedMultiplicity_hasKnownParitySector_structural
    G hfree hv hneigh hlocal p

end

end Erdos85
