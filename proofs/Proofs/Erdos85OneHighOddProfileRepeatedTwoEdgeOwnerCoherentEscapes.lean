import Proofs.Erdos85OneHighOddProfileRepeatedTwoEdgeOwnerPair
import Proofs.Erdos85OneHighOddProfileRepeatedOwnerCoherentEscapes
import Proofs.Erdos85OneHighOddProfileRepeatedOwnerTargetCapacity

/-! # Two distinct escaped witnesses exhaust one two-edge owner branch -/

namespace Erdos85

noncomputable section

/-- The structural package delivered by a repeated two-edge owner: two
different partition codes target the same exact branch, both force escapes
there, and their distinguished internal edges exhaust that branch. -/
def OneHighRepeatedTwoEdgeTargetCapacityWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V}
    (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (c d : Fin 3) : Prop :=
  ∃ q : OneHighPartitionLocalEdgeWitness G hfree hv p c,
    ∃ r : OneHighPartitionLocalEdgeWitness G hfree hv p d,
      q.t = r.t ∧
      oneHighFamilyInternalEdges p.profile (p.branchLabel q.t) = 2 ∧
      OneHighPartitionTargetEscape q ∧
      OneHighPartitionTargetEscape r ∧
      ∃ yq yr : OneHighMatchedBranchVertices G v q.t,
        yq ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t) ∧
        yr ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t) ∧
        yq ≠ yr ∧
        matchingEdgeSources (oneHighInternalMate G hfree v q.t) = {yq, yr}

/-- Consume one specified pair selected by the sharp finite classifier. -/
theorem oneHigh_twoEdgeOwnerPair_to_targetCapacityWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    {c d : Fin 3} (hcd : c ≠ d)
    (ec ed : Fin 8 × Fin 8) (owner : Fin 8)
    (hwc : OneHighRefinementOwnerPairWitness
      (oneHighGraphPairingRefinement G hfree hv p) c ec.1 ec.2)
    (hwd : OneHighRefinementOwnerPairWitness
      (oneHighGraphPairingRefinement G hfree hv p) d ed.1 ed.2)
    (hedges : oneHighFamilyInternalEdges p.profile owner = 2)
    (hownerc : owner ∈ ({ec.1, ec.2} : Finset (Fin 8)))
    (hownerd : owner ∈ ({ed.1, ed.2} : Finset (Fin 8))) :
    OneHighRepeatedTwoEdgeTargetCapacityWitness hv p c d := by
  obtain ⟨qc, hqcs, hqct⟩ :=
    oneHigh_graphOwnerPairWitness_to_partitionLocalEdgeWitness
      G hfree hv p c ec.1 ec.2 hwc
  obtain ⟨qd, hqds, hqdt⟩ :=
    oneHigh_graphOwnerPairWitness_to_partitionLocalEdgeWitness
      G hfree hv p d ed.1 ed.2 hwd
  let z := p.branchLabel.symm owner
  have hzmemc : z ∈ ({qc.s, qc.t} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hownerc ⊢
    rcases hownerc with h | h
    · left; apply p.branchLabel.injective; simpa [z, hqcs] using h
    · right; apply p.branchLabel.injective; simpa [z, hqct] using h
  have hzmemd : z ∈ ({qd.s, qd.t} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hownerd ⊢
    rcases hownerd with h | h
    · left; apply p.branchLabel.injective; simpa [z, hqds] using h
    · right; apply p.branchLabel.injective; simpa [z, hqdt] using h
  obtain ⟨qc', qd', hqctarget, hqdtarget, hescapeC, hescapeD⟩ :=
    oneHigh_exists_oriented_targetEscapes qc qd z hzmemc hzmemd
  have htarget : qc'.t = qd'.t := hqctarget.trans hqdtarget.symm
  have hedgeTarget : oneHighFamilyInternalEdges p.profile
      (p.branchLabel qc'.t) = 2 := by
    simpa [hqctarget, z] using hedges
  obtain ⟨yc, yd, hyc, hyd, hyne⟩ :=
    oneHigh_orientedDistinctCodes_exists_distinctTargetSources
      qc' qd' htarget hcd
  have hexhaust :=
    oneHigh_matchingEdgeSources_eq_pair_of_internalEdges_eq_two
      G hfree p qc'.t hedgeTarget yc yd hyc hyd hyne
  exact ⟨qc', qd', htarget, hedgeTarget, hescapeC, hescapeD,
    yc, yd, hyc, hyd, hyne, hexhaust⟩

/-- Every odd-profile all-even graph refinement has the exhausted shared
two-edge target package for some two distinct partition codes. -/
theorem oneHigh_oddProfile_exists_repeatedTwoEdgeTargetCapacityWitness
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
      OneHighRepeatedTwoEdgeTargetCapacityWitness hv p c d := by
  have hsel := oneHigh_oddProfile_graphPairing_has_repeatedTwoEdgeOwnerSelection
    G hfree hv p hprofile heven stored hstored hagree
  obtain ⟨e₀, e₁, e₂, hw₀, hw₁, hw₂, owner, hedge, hshared⟩ :=
    oneHigh_repeatedTwoEdgeOwnerSelection_exists_pairwise_shared _ _ hsel
  rcases hshared with h01 | h02 | h12
  · exact ⟨0, 1, by decide,
      oneHigh_twoEdgeOwnerPair_to_targetCapacityWitness
        G hfree hv p (by decide) e₀ e₁ owner hw₀ hw₁ hedge h01.1 h01.2⟩
  · exact ⟨0, 2, by decide,
      oneHigh_twoEdgeOwnerPair_to_targetCapacityWitness
        G hfree hv p (by decide) e₀ e₂ owner hw₀ hw₂ hedge h02.1 h02.2⟩
  · exact ⟨1, 2, by decide,
      oneHigh_twoEdgeOwnerPair_to_targetCapacityWitness
        G hfree hv p (by decide) e₁ e₂ owner hw₁ hw₂ hedge h12.1 h12.2⟩

end

end Erdos85

#print axioms Erdos85.oneHigh_twoEdgeOwnerPair_to_targetCapacityWitness
#print axioms Erdos85.oneHigh_oddProfile_exists_repeatedTwoEdgeTargetCapacityWitness
