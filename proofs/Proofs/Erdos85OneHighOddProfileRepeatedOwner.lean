import Proofs.Erdos85OneHighOddProfilePartitionGeometry

/-!
# A repeated exact owner among the three odd-profile partitions

The star-or-triangle quotient split alone permits six distinct root labels in
the triangle case.  The exact odd-profile refinement inventory is stronger:
the three transversal witnesses can always be selected so that one of their
six owner labels repeats.  This is the finite coherence needed to place two
forced target escapes in the same actual five-vertex branch.
-/

namespace Erdos85

private def oneHighOwnerPairWitnessDecidable
    (refinement : List (List OneHighLabelPair)) (code : Fin 3)
    (i j : Fin 8) : Decidable
      (OneHighRefinementOwnerPairWitness refinement code i j) := by
  unfold OneHighRefinementOwnerPairWitness
  infer_instance

/-- Computable list of the owner pairs witnessing one partition code. -/
def oneHighOwnerPairWitnessCandidates
    (refinement : List (List OneHighLabelPair)) (code : Fin 3) :
    List (Fin 8 × Fin 8) :=
  ((List.ofFn id : List (Fin 8)).product (List.ofFn id)).filter fun ij =>
    @decide (OneHighRefinementOwnerPairWitness refinement code ij.1 ij.2)
      (oneHighOwnerPairWitnessDecidable refinement code ij.1 ij.2)

/-- Whether one may select a witness for each partition code with fewer than
six distinct exact owner labels. -/
def oneHighRefinementHasRepeatedOwnerSelection
    (refinement : List (List OneHighLabelPair)) : Bool :=
  (oneHighOwnerPairWitnessCandidates refinement 0).any fun e₀ =>
    (oneHighOwnerPairWitnessCandidates refinement 1).any fun e₁ =>
      (oneHighOwnerPairWitnessCandidates refinement 2).any fun e₂ =>
        [e₀.1, e₀.2, e₁.1, e₁.2, e₂.1, e₂.2].toFinset.card < 6

/-- Propositional decoding of the executable repeated-owner selector. -/
theorem oneHighRefinementHasRepeatedOwnerSelection_eq_true_iff
    (refinement : List (List OneHighLabelPair)) :
    oneHighRefinementHasRepeatedOwnerSelection refinement = true ↔
      ∃ e₀ ∈ oneHighOwnerPairWitnessCandidates refinement 0,
        ∃ e₁ ∈ oneHighOwnerPairWitnessCandidates refinement 1,
          ∃ e₂ ∈ oneHighOwnerPairWitnessCandidates refinement 2,
            [e₀.1, e₀.2, e₁.1, e₁.2, e₂.1, e₂.2].toFinset.card < 6 := by
  simp [oneHighRefinementHasRepeatedOwnerSelection]

/-- Every profile-one all-even refinement has a simultaneous three-partition
selection with a repeated exact owner label. -/
theorem oneHigh_profileOne_allEven_has_repeatedOwnerSelection :
    ∀ table ∈ oneHighCapacityInventoryTables 1,
      ∀ refinement ∈ oneHighPairingRefinements 1
          (oneHighPairingTableRestrict table),
        oneHighRefinementAllOffDiagonalEven refinement = true →
          oneHighRefinementHasRepeatedOwnerSelection refinement = true := by
  native_decide

/-- Profile three has the same repeated exact owner property. -/
theorem oneHigh_profileThree_allEven_has_repeatedOwnerSelection :
    ∀ table ∈ oneHighCapacityInventoryTables 3,
      ∀ refinement ∈ oneHighPairingRefinements 3
          (oneHighPairingTableRestrict table),
        oneHighRefinementAllOffDiagonalEven refinement = true →
          oneHighRefinementHasRepeatedOwnerSelection refinement = true := by
  native_decide

/-- Graph-facing transport of the exact repeated-owner classification. -/
theorem oneHigh_oddProfile_graphPairing_has_repeatedOwnerSelection
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
    oneHighRefinementHasRepeatedOwnerSelection
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
  · exact oneHigh_profileOne_allEven_has_repeatedOwnerSelection stored
      (by simpa [hprofile] using hstored)
      (oneHighGraphPairingRefinement G hfree hv p)
      (by simpa [hprofile] using hrefinementStored) hallEven
  · exact oneHigh_profileThree_allEven_has_repeatedOwnerSelection stored
      (by simpa [hprofile] using hstored)
      (oneHighGraphPairingRefinement G hfree hv p)
      (by simpa [hprofile] using hrefinementStored) hallEven

end Erdos85

#print axioms Erdos85.oneHighRefinementHasRepeatedOwnerSelection_eq_true_iff
#print axioms Erdos85.oneHigh_profileOne_allEven_has_repeatedOwnerSelection
#print axioms Erdos85.oneHigh_profileThree_allEven_has_repeatedOwnerSelection
#print axioms Erdos85.oneHigh_oddProfile_graphPairing_has_repeatedOwnerSelection
