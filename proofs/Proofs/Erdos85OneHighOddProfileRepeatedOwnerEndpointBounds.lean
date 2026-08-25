import Proofs.Erdos85OneHighOddProfileRepeatedTwoEdgeOwnerSpecifiedEscapes
import Proofs.Erdos85OneHighRepeatedOwnerPairingEndpointBound

/-! # Endpoint bounds at the repeated two-edge owner

The two exact keys selected by unequal odd-profile partition codes exhaust the
shared target matching.  Consequently, each opposing source label occurs at
most once among the endpoints of the target branch's complete pairing.  This
is a graph-facing refinement restriction; it is not by itself a contradiction.
-/

namespace Erdos85

noncomputable section

/-- A coherently oriented unequal-code pair at a two-edge target bounds both
opposing source labels in the target branch's complete pairing. -/
theorem oneHigh_orientedTwoEdgePair_endpointCounts_le_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {c d : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p c)
    (r : OneHighPartitionLocalEdgeWitness G hfree hv p d)
    (htarget : q.t = r.t) (hcode : c ≠ d)
    (hedges : oneHighFamilyInternalEdges p.profile
      (p.branchLabel q.t) = 2) :
    oneHighPairingEndpointCount
        (oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.t))
        (p.branchLabel q.s) ≤ 1 ∧
      oneHighPairingEndpointCount
        (oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.t))
        (p.branchLabel r.s) ≤ 1 := by
  rcases q.edge_data with ⟨keyq, hqLt, hqNonmate, hqFarS, hqFarT,
    xq, hxq, hxqKey, yq, hyq, hyqKey⟩
  rcases r.edge_data with ⟨keyr, hrLt, hrNonmate, hrFarS, hrFarT,
    xr, hxr, hxrKey, yr, hyr, hyrKey⟩
  have hqReverseMate : q.s ≠ p.mate q.t := by
    intro h
    apply q.target_ne_mate
    have hm := congrArg p.mate h
    simpa [p.mate_involutive q.t] using hm.symm
  have hrReverseMate : r.s ≠ p.mate r.t := by
    intro h
    apply r.target_ne_mate
    have hm := congrArg p.mate h
    simpa [p.mate_involutive r.t] using hm.symm
  have hqCode : oneHighOwnerPartitionCode
      (p.branchLabel q.t) (p.branchLabel q.s) = c := by
    rw [← oneHighOwnerPartitionCode_comm]
    exact of_decide_eq_true q.code_eq
  have hrCode : oneHighOwnerPartitionCode
      (p.branchLabel r.t) (p.branchLabel r.s) = d := by
    rw [← oneHighOwnerPartitionCode_comm]
    exact of_decide_eq_true r.code_eq
  have hcodeNe : oneHighOwnerPartitionCode
      (p.branchLabel q.t) (p.branchLabel q.s) ≠
      oneHighOwnerPartitionCode (p.branchLabel q.t) (p.branchLabel r.s) := by
    intro h
    apply hcode
    rw [← hqCode, ← hrCode]
    simpa [htarget] using h
  have hkeys : keyq ≠ keyr :=
    oneHigh_sharedOwner_unequalPartitionCode_keys_ne
      (p.branchLabel q.t) (p.branchLabel q.s) (p.branchLabel r.s)
      keyq keyr
      (fun h => q.source_ne (p.branchLabel.injective h.symm))
      (by
        intro h
        apply hqReverseMate
        apply p.branchLabel.injective
        simpa [p.branch_mate] using h)
      (fun h => r.source_ne (p.branchLabel.injective (htarget ▸ h).symm))
      (by
        intro h
        apply hrReverseMate
        apply p.branchLabel.injective
        simpa [p.branch_mate, htarget] using h)
      hqLt hqNonmate hqFarT hqFarS
      hrLt hrNonmate (by simpa [htarget] using hrFarT) hrFarS hcodeNe
  let yrq := oneHighMatchedBranchTransport G v htarget.symm yr
  have hyrq : yrq ∈
      matchingEdgeSources (oneHighInternalMate G hfree v q.t) :=
    oneHighMatchedBranchTransport_mem_matchingEdgeSources
      G hfree htarget.symm yr hyr
  have hyrqKey' : oneHighTargetMissKey G hfree hv p q.t yrq = keyr := by
    rw [oneHighTargetMissKey_transport G hfree hv p htarget.symm yr]
    exact hyrKey
  have hyne : yq ≠ yrq := by
    intro heq
    apply hkeys
    exact hyqKey.symm.trans
      ((congrArg (oneHighTargetMissKey G hfree hv p q.t) heq).trans hyrqKey')
  have hexhaust :=
    oneHigh_matchingEdgeSources_eq_pair_of_internalEdges_eq_two
      G hfree p q.t hedges yq yrq hyq hyrq hyne
  have hyrqKey :
      (min
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.t yrq))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.t
              (oneHighInternalMate G hfree v q.t yrq))),
        max
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.t yrq))
          (p.branchLabel (oneHighMatchedMissLabel G hfree hv
            p.external_empty p.outer_degree p.mate p.mate_adj q.t
              (oneHighInternalMate G hfree v q.t yrq)))) = keyr := by
    change oneHighTargetMissKey G hfree hv p q.t yrq = keyr
    exact hyrqKey'
  have hqBound := oneHighPairingEndpointCount_le_one_of_exhausted_pair
    (oneHighInternalMate G hfree v q.t)
    (fun y => p.branchLabel
      (oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj q.t y))
    yq yrq hyq hyrq hyne hexhaust keyq keyr (p.branchLabel q.s)
    hyqKey
    hyrqKey
    hqFarS hkeys hrLt
  have hrBound := oneHighPairingEndpointCount_le_one_of_exhausted_pair
    (oneHighInternalMate G hfree v q.t)
    (fun y => p.branchLabel
      (oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj q.t y))
    yrq yq hyrq hyq hyne.symm (by simpa [Finset.pair_comm] using hexhaust)
    keyr keyq (p.branchLabel r.s)
    hyrqKey
    hyqKey (by simpa [htarget] using hrFarS) hkeys.symm hqLt
  unfold oneHighGraphSourcePairing
  rw [p.branchLabel.symm_apply_apply]
  exact ⟨hqBound, hrBound⟩

/-- Every graph-realized all-even odd profile supplies an unequal selected
pair at a shared two-edge owner satisfying both endpoint bounds. -/
theorem oneHigh_oddProfile_exists_repeatedOwner_endpointCounts_le_one
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
    ∃ c d : Fin 3, c ≠ d ∧
      ∃ q : OneHighPartitionLocalEdgeWitness G hfree hv p c,
        ∃ r : OneHighPartitionLocalEdgeWitness G hfree hv p d,
          q.t = r.t ∧
          oneHighPairingEndpointCount
              (oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.t))
              (p.branchLabel q.s) ≤ 1 ∧
          oneHighPairingEndpointCount
              (oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.t))
              (p.branchLabel r.s) ≤ 1 := by
  obtain ⟨c, d, hcd, q, r, htarget, hedges, -, -, -, -⟩ :=
    oneHigh_oddProfile_exists_repeatedTwoEdgeTargetCapacityWitness
      G hfree hv p hprofile heven stored hstored hagree
  exact ⟨c, d, hcd, q, r, htarget,
    oneHigh_orientedTwoEdgePair_endpointCounts_le_one
      q r htarget hcd hedges⟩

end

end Erdos85

#print axioms Erdos85.oneHigh_orientedTwoEdgePair_endpointCounts_le_one
#print axioms Erdos85.oneHigh_oddProfile_exists_repeatedOwner_endpointCounts_le_one
