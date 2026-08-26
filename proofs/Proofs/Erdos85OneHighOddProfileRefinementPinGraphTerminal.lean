import Proofs.Erdos85OneHighGraphCanonicalSlotCoverage
import Proofs.Erdos85OneHighOddProfileRefinementPinTerminal

/-! # Graph-facing odd-profile refinement-pin terminal -/

namespace Erdos85

noncomputable section

/-- A complete checked odd-profile refinement-pin bank excludes an all-even
one-high graph directly.  Canonical-slot compatibility is supplied by the
graph construction, rather than remaining as an external hypothesis. -/
theorem false_of_oneHigh_oddProfile_allEven_refinementPinBank_graph
    (hbank : OneHighOddProfileRefinementPinBank)
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hprofile : p.profile = 1 ∨ p.profile = 3)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key))
    (stored : OneHighMissTable)
    (hstored : stored ∈ oneHighCapacityInventoryTables
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩)
    (hagree : OneHighTableRelevantAgree
      (oneHighFamilyGraphTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) stored) : False := by
  exact false_of_oneHigh_oddProfile_allEven_refinementPinBank hbank
    G hfree hv p hprofile heven stored hstored hagree
    (oneHighGraphCanonicalSlotRefinement_slotCompatible G hfree hv p)

end

end Erdos85

#print axioms Erdos85.false_of_oneHigh_oddProfile_allEven_refinementPinBank_graph
