import Proofs.Erdos85OneHighOddProfileRepeatedOwner

/-!
# A repeated owner with two internal edges in odd one-high profiles

The exact owner repeated across two partition witnesses cannot always be
chosen in a one-edge branch.  The complementary sharp statement does hold:
one can always choose the three witnesses so that a repeated exact owner is
a two-internal-edge branch.  Thus the two selected source edges in that
branch are either the same edge or exhaust its two-edge matching.
-/

namespace Erdos85

/-- Executable selector for three partition witnesses having an exact owner
which occurs at least twice and belongs to a two-internal-edge branch. -/
def oneHighRefinementHasRepeatedTwoEdgeOwnerSelection
    (profile : Fin 5) (refinement : List (List OneHighLabelPair)) : Bool :=
  (oneHighOwnerPairWitnessCandidates refinement 0).any fun e₀ =>
    (oneHighOwnerPairWitnessCandidates refinement 1).any fun e₁ =>
      (oneHighOwnerPairWitnessCandidates refinement 2).any fun e₂ =>
        let owners := [e₀.1, e₀.2, e₁.1, e₁.2, e₂.1, e₂.2]
        owners.any fun owner =>
          oneHighFamilyInternalEdges profile.val owner == 2 &&
            2 <= owners.count owner

/-- Propositional decoder retaining the three chosen pairs and the repeated
two-edge owner. -/
theorem oneHighRefinementHasRepeatedTwoEdgeOwnerSelection_eq_true_iff
    (profile : Fin 5) (refinement : List (List OneHighLabelPair)) :
    oneHighRefinementHasRepeatedTwoEdgeOwnerSelection profile refinement = true ↔
      ∃ e₀ ∈ oneHighOwnerPairWitnessCandidates refinement 0,
        ∃ e₁ ∈ oneHighOwnerPairWitnessCandidates refinement 1,
          ∃ e₂ ∈ oneHighOwnerPairWitnessCandidates refinement 2,
            ∃ owner ∈ [e₀.1, e₀.2, e₁.1, e₁.2, e₂.1, e₂.2],
              oneHighFamilyInternalEdges profile.val owner = 2 ∧
                2 <= [e₀.1, e₀.2, e₁.1, e₁.2, e₂.1, e₂.2].count owner := by
  simp [oneHighRefinementHasRepeatedTwoEdgeOwnerSelection, beq_iff_eq]

set_option maxHeartbeats 0 in
/-- Every profile-one all-even refinement admits the sharp two-edge repeated
owner selection. -/
theorem oneHigh_profileOne_allEven_has_repeatedTwoEdgeOwnerSelection :
    ∀ table ∈ oneHighCapacityInventoryTables 1,
      ∀ refinement ∈ oneHighPairingRefinements 1
          (oneHighPairingTableRestrict table),
        oneHighRefinementAllOffDiagonalEven refinement = true →
          oneHighRefinementHasRepeatedTwoEdgeOwnerSelection 1 refinement = true := by
  native_decide

set_option maxHeartbeats 0 in
/-- Profile three has the same sharp selection property. -/
theorem oneHigh_profileThree_allEven_has_repeatedTwoEdgeOwnerSelection :
    ∀ table ∈ oneHighCapacityInventoryTables 3,
      ∀ refinement ∈ oneHighPairingRefinements 3
          (oneHighPairingTableRestrict table),
        oneHighRefinementAllOffDiagonalEven refinement = true →
          oneHighRefinementHasRepeatedTwoEdgeOwnerSelection 3 refinement = true := by
  native_decide

/-- Graph-facing transport of the repeated two-edge-owner classification. -/
theorem oneHigh_oddProfile_graphPairing_has_repeatedTwoEdgeOwnerSelection
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
    oneHighRefinementHasRepeatedTwoEdgeOwnerSelection
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
      (oneHighGraphPairingRefinement G hfree hv p) = true := by
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
  · simpa [hprofile] using
      (oneHigh_profileOne_allEven_has_repeatedTwoEdgeOwnerSelection stored
        (by simpa [hprofile] using hstored)
        (oneHighGraphPairingRefinement G hfree hv p)
        (by simpa [hprofile] using hrefinementStored) hallEven)
  · simpa [hprofile] using
      (oneHigh_profileThree_allEven_has_repeatedTwoEdgeOwnerSelection stored
        (by simpa [hprofile] using hstored)
        (oneHighGraphPairingRefinement G hfree hv p)
        (by simpa [hprofile] using hrefinementStored) hallEven)

end Erdos85

#print axioms Erdos85.oneHighRefinementHasRepeatedTwoEdgeOwnerSelection_eq_true_iff
#print axioms Erdos85.oneHigh_profileOne_allEven_has_repeatedTwoEdgeOwnerSelection
#print axioms Erdos85.oneHigh_profileThree_allEven_has_repeatedTwoEdgeOwnerSelection
#print axioms Erdos85.oneHigh_oddProfile_graphPairing_has_repeatedTwoEdgeOwnerSelection
