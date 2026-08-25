import Proofs.Erdos85OneHighOddProfileSeparatedRepeat

/-!
# Code-preserving local edges for odd one-high profiles

This is the concrete graph bridge for the simultaneous three-partition
classification: it inverts a witness for a prescribed partition code to the
two internal matching edges which carry its repeated key.
-/

namespace Erdos85

theorem oneHigh_oddProfile_exists_partitionLocalEdges
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
    (code : Fin 3) :
    ∃ s t : {z : V // z ∈ G.neighborSet v},
      s ≠ t ∧ t ≠ p.mate s ∧
      (oneHighOwnerPartitionCode (p.branchLabel s) (p.branchLabel t) ==
        code) = true ∧
      ∃ key : OneHighLabelPair,
        key.1 < key.2 ∧
        key.2 ≠ oneHighStandardMate key.1 ∧
        OneHighKeyFarFromSource key (p.branchLabel s) ∧
        OneHighKeyFarFromSource key (p.branchLabel t) ∧
        ∃ x ∈ matchingEdgeSources (oneHighInternalMate G hfree v s),
          (min (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj s x))
              (p.branchLabel (oneHighMatchedMissLabel G hfree hv
                p.external_empty p.outer_degree p.mate p.mate_adj s
                  (oneHighInternalMate G hfree v s x))),
            max (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj s x))
              (p.branchLabel (oneHighMatchedMissLabel G hfree hv
                p.external_empty p.outer_degree p.mate p.mate_adj s
                  (oneHighInternalMate G hfree v s x)))) = key ∧
        ∃ y ∈ matchingEdgeSources (oneHighInternalMate G hfree v t),
          (min (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj t y))
              (p.branchLabel (oneHighMatchedMissLabel G hfree hv
                p.external_empty p.outer_degree p.mate p.mate_adj t
                  (oneHighInternalMate G hfree v t y))),
            max (p.branchLabel (oneHighMatchedMissLabel G hfree hv
              p.external_empty p.outer_degree p.mate p.mate_adj t y))
              (p.branchLabel (oneHighMatchedMissLabel G hfree hv
                p.external_empty p.outer_degree p.mate p.mate_adj t
                  (oneHighInternalMate G hfree v t y)))) = key := by
  obtain ⟨i, j, hij, hjmate, hcode, key, hkeylt, hkeyNonmate,
    hkeyFarI, hkeyFarJ, hkeyi, hkeyj⟩ :=
    oneHigh_oddProfile_graphPairing_has_all_transversalPartitions
      G hfree hv p hprofile heven stored hstored hagree code
  have hgeti : (oneHighGraphPairingRefinement G hfree hv p).getD i.val [] =
      oneHighGraphSourcePairing G hfree hv p i := by
    fin_cases i <;> rfl
  have hgetj : (oneHighGraphPairingRefinement G hfree hv p).getD j.val [] =
      oneHighGraphSourcePairing G hfree hv p j := by
    fin_cases j <;> rfl
  have hkeyi' : key ∈ oneHighGraphSourcePairing G hfree hv p i := by
    rwa [hgeti] at hkeyi
  have hkeyj' : key ∈ oneHighGraphSourcePairing G hfree hv p j := by
    rwa [hgetj] at hkeyj
  let s := p.branchLabel.symm i
  let t := p.branchLabel.symm j
  have hst : s ≠ t := by
    intro h
    apply hij
    simpa [s, t] using congrArg p.branchLabel h
  have htMate : t ≠ p.mate s := by
    intro h
    apply hjmate
    have := congrArg p.branchLabel h
    simpa [s, t, p.branch_mate] using this
  have hcodeST :
      (oneHighOwnerPartitionCode (p.branchLabel s) (p.branchLabel t) ==
        code) = true := by
    simpa [s, t] using hcode
  change key ∈ matchingPairingListSorted
      (oneHighInternalMate G hfree v s)
      (fun x => p.branchLabel (oneHighMatchedMissLabel G hfree hv
        p.external_empty p.outer_degree p.mate p.mate_adj s x)) at hkeyi'
  change key ∈ matchingPairingListSorted
      (oneHighInternalMate G hfree v t)
      (fun x => p.branchLabel (oneHighMatchedMissLabel G hfree hv
        p.external_empty p.outer_degree p.mate p.mate_adj t x)) at hkeyj'
  obtain ⟨x, hx, hxkey⟩ :=
    exists_matchingEdgeSource_of_mem_matchingPairingListSorted _ _ hkeyi'
  obtain ⟨y, hy, hykey⟩ :=
    exists_matchingEdgeSource_of_mem_matchingPairingListSorted _ _ hkeyj'
  have hkeyFarS : OneHighKeyFarFromSource key (p.branchLabel s) := by
    simpa [s] using hkeyFarI
  have hkeyFarT : OneHighKeyFarFromSource key (p.branchLabel t) := by
    simpa [t] using hkeyFarJ
  exact ⟨s, t, hst, htMate, hcodeST, key, hkeylt, hkeyNonmate,
    hkeyFarS, hkeyFarT, x, hx, hxkey, y, hy, hykey⟩

end Erdos85

#print axioms Erdos85.oneHigh_oddProfile_exists_partitionLocalEdges
