import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85OneHighOddProfileSlotVariantCoverage
import Proofs.Erdos85OneHighRefinementPinnedExclusion

/-! # Profile-specific checked refinement-pin bank -/

namespace Erdos85

noncomputable section

/-- Checked UNSAT evidence for every profile-one/profile-three canonical-slot
variant.  Keeping the profile-specific membership in the interface prevents a
certificate for one profile from being applied to the same literal list under
the other profile's CNF. -/
def OneHighOddProfileRefinementPinBank : Prop :=
  ∀ profile : Fin 5, profile = 1 ∨ profile = 3 →
    ∀ refinement,
      refinement ∈
          (oneHighAllEvenCapacityInventoryRefinements profile).flatMap
            oneHighRefinementSlotVariants →
        OneHighRefinementCheckedUnsat profile.val refinement

/-- The graph's sorted pairing refinement belongs to the exact all-even
capacity inventory attached to any stored orbit representative agreeing with
its relevant miss table. -/
theorem oneHighGraphPairingRefinement_mem_allEvenCapacityInventoryRefinements
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
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
        p.profile) stored) :
    oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighAllEvenCapacityInventoryRefinements
        ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩ := by
  let profile : Fin 5 :=
    ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
  let table := oneHighGraphRelevantMissTable
    (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)) p.profile
  have hstoredAll : stored ∈
      oneHighAllEvenCapacityInventoryTables profile :=
    oneHigh_storedTable_mem_allEvenCapacityInventory
      G hfree hv p heven stored hstored hagree
  have htableRestrict : oneHighPairingTableRestrict table = table :=
    oneHighTableRestrict_graphRelevantMissTable _ _
  have hrel : OneHighTableRelevantAgree table stored :=
    oneHighGraphRelevantMissTable_relevantAgree_of_graphTable _ _ hagree
  have hrestrictEq : oneHighPairingTableRestrict table =
      oneHighPairingTableRestrict stored :=
    oneHighPairingTableRestrict_eq_of_relevantAgree hrel
  have hrefinement : oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighPairingRefinements p.profile table :=
    oneHighGraphPairingRefinement_mem G hfree hv p
  have hrefinementStored : oneHighGraphPairingRefinement G hfree hv p ∈
      oneHighPairingRefinements p.profile
        (oneHighPairingTableRestrict stored) := by
    rw [htableRestrict] at hrestrictEq
    rwa [hrestrictEq] at hrefinement
  have hallEven : oneHighRefinementAllOffDiagonalEven
      (oneHighGraphPairingRefinement G hfree hv p) = true :=
    oneHighGraphPairingRefinement_allOffDiagonalEven G hfree hv p heven
  rw [oneHighAllEvenCapacityInventoryRefinements]
  exact List.mem_flatMap.mpr
    ⟨stored, hstoredAll, List.mem_filter.mpr ⟨hrefinementStored, hallEven⟩⟩

end

end Erdos85

#print axioms Erdos85.oneHighGraphPairingRefinement_mem_allEvenCapacityInventoryRefinements
