import Proofs.Erdos85OneHighGraphCanonicalSlotRefinement
import Proofs.Erdos85OneHighOddProfileRefinementPinBank

/-!
# Terminal socket for the odd-profile refinement-pin certificate bank

The executable bank is indexed by the profile-specific slot expansion, not
merely by the combined 122-element list.  This file records that exact
interface and transports an all-even graph presentation into it.
-/

namespace Erdos85

noncomputable section

/-- A complete checked odd-profile slot bank excludes an all-even graph as
soon as its literal canonical slots are shown compatible with the sorted
pairing refinement. -/
theorem false_of_oneHigh_oddProfile_allEven_refinementPinBank
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
        p.profile) stored)
    (hslots : OneHighRefinementSlotCompatible
      (oneHighGraphPairingRefinement G hfree hv p)
      (oneHighGraphCanonicalSlotRefinement G hfree p)) : False := by
  let profile : Fin 5 :=
    ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
  have hprofileFin : profile = 1 ∨ profile = 3 := by
    rcases hprofile with h | h
    · left
      apply Fin.ext
      simpa [profile] using h
    · right
      apply Fin.ext
      simpa [profile] using h
  have hsorted :=
    oneHighGraphPairingRefinement_mem_allEvenCapacityInventoryRefinements
      G hfree hv p heven stored hstored hagree
  have hvariant : oneHighGraphCanonicalSlotRefinement G hfree p ∈
      (oneHighAllEvenCapacityInventoryRefinements profile).flatMap
        oneHighRefinementSlotVariants :=
    oneHigh_slotVariant_mem_profile hsorted hslots
  have hchecked : OneHighRefinementCheckedUnsat p.profile
      (oneHighGraphCanonicalSlotRefinement G hfree p) := by
    simpa [profile] using hbank profile hprofileFin _ hvariant
  exact false_of_oneHighRefinementCheckedUnsat hchecked
    (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
    p.constraints
    (oneHighGraphCanonicalSlotRefinement_pinSemantics G hfree hv p)

end

end Erdos85

#print axioms Erdos85.false_of_oneHigh_oddProfile_allEven_refinementPinBank
