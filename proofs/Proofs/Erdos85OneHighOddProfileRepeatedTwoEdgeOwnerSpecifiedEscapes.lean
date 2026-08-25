import Proofs.Erdos85OneHighOddProfileRepeatedTwoEdgeOwnerCoherentEscapes
import Proofs.Erdos85OneHighOddProfileSpecifiedPartitionEscape

/-! # Coherent escapes from the two edges exhausting a repeated owner -/

namespace Erdos85

noncomputable section

/-- The fixed-edge conclusion of the specified partition escape theorem. -/
def OneHighSpecifiedTargetEscape
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {code : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p code)
    (x : OneHighMatchedBranchVertices G v q.s)
    (y : OneHighMatchedBranchVertices G v q.t) : Prop :=
  ∃ a b : V,
    a ∈ secondLayerBranch G v q.t ∧
    b ∈ secondLayerBranch G v q.t ∧
    G.Adj x.1.1 a ∧
    G.Adj (oneHighInternalMate G hfree v q.s x).1.1 b ∧
    a ≠ b ∧ ¬ G.Adj a b ∧
    ((a ≠ y.1.1 ∧
        a ≠ (oneHighInternalMate G hfree v q.t y).1.1) ∨
      (b ≠ y.1.1 ∧
        b ≠ (oneHighInternalMate G hfree v q.t y).1.1))

/-- The fully coherent terminal package: after transporting the second
target-edge source into the first witness's branch type, those two exact
edges exhaust the two-edge branch, and each witness's forced escape is tied
to its corresponding edge. -/
def OneHighSpecifiedTwoEdgeEscapePair
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {c d : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p c)
    (r : OneHighPartitionLocalEdgeWitness G hfree hv p d)
    (htarget : q.t = r.t) : Prop :=
  ∃ xq : OneHighMatchedBranchVertices G v q.s,
    ∃ yq : OneHighMatchedBranchVertices G v q.t,
      ∃ xr : OneHighMatchedBranchVertices G v r.s,
        ∃ yr : OneHighMatchedBranchVertices G v r.t,
          xq ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.s) ∧
          yq ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t) ∧
          xr ∈ matchingEdgeSources (oneHighInternalMate G hfree v r.s) ∧
          yr ∈ matchingEdgeSources (oneHighInternalMate G hfree v r.t) ∧
          yq ≠ oneHighMatchedBranchTransport G v htarget.symm yr ∧
          matchingEdgeSources (oneHighInternalMate G hfree v q.t) =
            {yq, oneHighMatchedBranchTransport G v htarget.symm yr} ∧
          OneHighSpecifiedTargetEscape q xq yq ∧
          OneHighSpecifiedTargetEscape r xr yr

/-- Destruct each `edge_data` field once, so distinctness, exhaustion, and
both escape conclusions all refer to the same two target edges. -/
theorem oneHigh_orientedTwoEdgePair_exists_specifiedEscapes
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {c d : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p c)
    (r : OneHighPartitionLocalEdgeWitness G hfree hv p d)
    (htarget : q.t = r.t) (hcode : c ≠ d)
    (hedges : oneHighFamilyInternalEdges p.profile
      (p.branchLabel q.t) = 2) :
    OneHighSpecifiedTwoEdgeEscapePair q r htarget := by
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
  have hyqKey' : oneHighTargetMissKey G hfree hv p q.t yq = keyq := hyqKey
  have hyrKey' : oneHighTargetMissKey G hfree hv p r.t yr = keyr := hyrKey
  have hyne : yq ≠ yrq := by
    intro heq
    apply hkeys
    rw [← hyqKey', ← hyrKey']
    rw [← oneHighTargetMissKey_transport G hfree hv p htarget.symm yr]
    exact congrArg (oneHighTargetMissKey G hfree hv p q.t) heq
  have hexhaust :=
    oneHigh_matchingEdgeSources_eq_pair_of_internalEdges_eq_two
      G hfree p q.t hedges yq yrq hyq hyrq hyne
  have hescapeQ : OneHighSpecifiedTargetEscape q xq yq :=
    q.exists_targetEscape_of_edgeData keyq hqLt hqFarT
      xq hxq hxqKey yq hyq
  have hescapeR : OneHighSpecifiedTargetEscape r xr yr :=
    r.exists_targetEscape_of_edgeData keyr hrLt hrFarT
      xr hxr hxrKey yr hyr
  exact ⟨xq, yq, xr, yr, hxq, hyq, hxr, hyr, hyne, hexhaust,
    hescapeQ, hescapeR⟩

/-- Upgrade the sharp odd-profile aggregate to the coherent specified-edge
escape package. -/
theorem oneHigh_oddProfile_exists_specifiedTwoEdgeEscapes
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
          ∃ htarget : q.t = r.t,
            oneHighFamilyInternalEdges p.profile (p.branchLabel q.t) = 2 ∧
            OneHighSpecifiedTwoEdgeEscapePair q r htarget := by
  obtain ⟨c, d, hcd, q, r, htarget, hedges, -, -, -, -⟩ :=
    oneHigh_oddProfile_exists_repeatedTwoEdgeTargetCapacityWitness
      G hfree hv p hprofile heven stored hstored hagree
  exact ⟨c, d, hcd, q, r, htarget, hedges,
    oneHigh_orientedTwoEdgePair_exists_specifiedEscapes
      q r htarget hcd hedges⟩

end

end Erdos85

#print axioms Erdos85.oneHigh_orientedTwoEdgePair_exists_specifiedEscapes
#print axioms Erdos85.oneHigh_oddProfile_exists_specifiedTwoEdgeEscapes
