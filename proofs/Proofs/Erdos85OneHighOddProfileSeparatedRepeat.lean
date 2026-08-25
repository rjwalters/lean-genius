import Proofs.Erdos85OneHighAllEvenCapacityInventory

/-! # Separated repeated keys in the odd one-high profiles

The abstract all-even argument produces two owners of one repeated exchanged
key, but its graph-facing residual originally retained three owner sectors:
equal, root-mate, and genuinely separated.  The exact capacity inventory
shows that profiles one and three always admit a witness in the strongest
sector.  This is a finite statement about the already-verified table and
pairing-refinement enumerators; it does not assert that the residual is
impossible.
-/

namespace Erdos85

/-- A compatible refinement contains the same off-diagonal key in two
distinct source rows which are not a standard mate pair. -/
def OneHighRefinementHasSeparatedRepeatedKey
    (refinement : List (List OneHighLabelPair)) : Prop :=
  ∃ i j : Fin 8,
    i ≠ j ∧ j ≠ oneHighStandardMate i ∧
      ∃ key : OneHighLabelPair,
        key.1 < key.2 ∧
        key ∈ refinement.getD i.val [] ∧
        key ∈ refinement.getD j.val []

instance (refinement : List (List OneHighLabelPair)) :
    Decidable (OneHighRefinementHasSeparatedRepeatedKey refinement) :=
  by
    unfold OneHighRefinementHasSeparatedRepeatedKey
    infer_instance

/-- No profile-one capacity row has an all-even compatible refinement whose
repeated off-diagonal keys are confined to one owner or a root-mate pair. -/
theorem oneHigh_profileOne_allEven_has_separatedRepeatedKey :
    ∀ table ∈ oneHighCapacityInventoryTables 1,
      ∀ refinement ∈ oneHighPairingRefinements 1
          (oneHighPairingTableRestrict table),
        oneHighRefinementAllOffDiagonalEven refinement = true →
          OneHighRefinementHasSeparatedRepeatedKey refinement := by
  native_decide

/-- Profile three has the same strongest-owner-sector conclusion. -/
theorem oneHigh_profileThree_allEven_has_separatedRepeatedKey :
    ∀ table ∈ oneHighCapacityInventoryTables 3,
      ∀ refinement ∈ oneHighPairingRefinements 3
          (oneHighPairingTableRestrict table),
        oneHighRefinementAllOffDiagonalEven refinement = true →
          OneHighRefinementHasSeparatedRepeatedKey refinement := by
  native_decide

/-- Graph-facing form of the finite classification.  Once an odd-profile
graph table is transported to any capacity representative, its actual global
pairing refinement has a repeated off-diagonal key in separated source rows.
This sharpens the owner trichotomy but is not itself a contradiction. -/
theorem oneHigh_oddProfile_graphPairing_has_separatedRepeatedKey
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
        p.profile) stored) :
    OneHighRefinementHasSeparatedRepeatedKey
      (oneHighGraphPairingRefinement G hfree hv p) := by
  let table := oneHighGraphRelevantMissTable
    (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)) p.profile
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
  rcases hprofile with hprofile | hprofile
  · exact oneHigh_profileOne_allEven_has_separatedRepeatedKey stored
      (by simpa [hprofile] using hstored)
      (oneHighGraphPairingRefinement G hfree hv p)
      (by simpa [hprofile] using hrefinementStored) hallEven
  · exact oneHigh_profileThree_allEven_has_separatedRepeatedKey stored
      (by simpa [hprofile] using hstored)
      (oneHighGraphPairingRefinement G hfree hv p)
      (by simpa [hprofile] using hrefinementStored) hallEven

end Erdos85
