import Proofs.Erdos85OneHighOddProfileRepeatedTwoEdgeOwnerPair
import Proofs.Erdos85OneHighOddProfileRepeatedOwnerCoherentEscapes
import Proofs.Erdos85OneHighOddProfileRepeatedOwnerTargetCapacity

/-! # Exhaust the repeated two-edge target branch -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Two unequal partition codes target the same two-edge branch, and their
distinguished target edges are exactly that branch's internal matching. -/
structure OneHighRepeatedTwoEdgeTargetExhaustion
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} (c d : Fin 3) where
  code_ne : c ≠ d
  z : {x : V // x ∈ G.neighborSet v}
  q : OneHighPartitionLocalEdgeWitness G hfree hv p c
  r : OneHighPartitionLocalEdgeWitness G hfree hv p d
  q_target : q.t = z
  r_target : r.t = z
  q_escape : OneHighPartitionTargetEscape q
  r_escape : OneHighPartitionTargetEscape r
  internalEdges : oneHighFamilyInternalEdges p.profile (p.branchLabel z) = 2
  yq : OneHighMatchedBranchVertices G v z
  yr : OneHighMatchedBranchVertices G v z
  yq_mem : yq ∈ matchingEdgeSources (oneHighInternalMate G hfree v z)
  yr_mem : yr ∈ matchingEdgeSources (oneHighInternalMate G hfree v z)
  sources_ne : yq ≠ yr
  exhausts : matchingEdgeSources (oneHighInternalMate G hfree v z) = {yq, yr}

private theorem oneHigh_pairwiseShared_exists_targetExhaustion
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {c d : Fin 3}
    (hcd : c ≠ d) (i j k l owner : Fin 8)
    (hi : OneHighRefinementOwnerPairWitness
      (oneHighGraphPairingRefinement G hfree hv p) c i j)
    (hk : OneHighRefinementOwnerPairWitness
      (oneHighGraphPairingRefinement G hfree hv p) d k l)
    (hoi : owner ∈ ({i, j} : Finset (Fin 8)))
    (hok : owner ∈ ({k, l} : Finset (Fin 8)))
    (hedges : oneHighFamilyInternalEdges p.profile owner = 2) :
    Nonempty (OneHighRepeatedTwoEdgeTargetExhaustion
      (G := G) (hfree := hfree) (hv := hv) (p := p) c d) := by
  obtain ⟨q, hqs, hqt⟩ :=
    oneHigh_graphOwnerPairWitness_to_partitionLocalEdgeWitness
      G hfree hv p c i j hi
  obtain ⟨r, hrs, hrt⟩ :=
    oneHigh_graphOwnerPairWitness_to_partitionLocalEdgeWitness
      G hfree hv p d k l hk
  let z := p.branchLabel.symm owner
  have hzq : z ∈ ({q.s, q.t} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hoi ⊢
    rcases hoi with hoi | hoi
    · left
      apply p.branchLabel.injective
      simpa [z, hqs] using hoi
    · right
      apply p.branchLabel.injective
      simpa [z, hqt] using hoi
  have hzr : z ∈ ({r.s, r.t} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hok ⊢
    rcases hok with hok | hok
    · left
      apply p.branchLabel.injective
      simpa [z, hrs] using hok
    · right
      apply p.branchLabel.injective
      simpa [z, hrt] using hok
  obtain ⟨q', r', hqz, hrz, hqe, hre⟩ :=
    oneHigh_exists_oriented_targetEscapes q r z hzq hzr
  have hedgeZ : oneHighFamilyInternalEdges p.profile (p.branchLabel z) = 2 := by
    simpa [z] using hedges
  have hedgeQ : oneHighFamilyInternalEdges p.profile (p.branchLabel q'.t) = 2 := by
    rw [hqz]
    exact hedgeZ
  have htargets : q'.t = r'.t := hqz.trans hrz.symm
  obtain ⟨yq, yr, hyq, hyr, hne⟩ :=
    oneHigh_orientedDistinctCodes_exists_distinctTargetSources
      q' r' htargets hcd
  have hexhaust := oneHigh_matchingEdgeSources_eq_pair_of_internalEdges_eq_two
    G hfree p q'.t hedgeQ yq yr hyq hyr hne
  exact ⟨⟨hcd, q'.t, q', r', rfl, htargets.symm, hqe, hre, hedgeQ,
    yq, yr, hyq, hyr, hne, hexhaust⟩⟩

/-- In every odd-profile all-even refinement, a specified unequal pair among
codes `01`, `02`, or `12` exhausts one actual two-edge target branch. -/
theorem oneHigh_oddProfile_exists_repeatedTwoEdgeTargetExhaustion
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
    Nonempty (OneHighRepeatedTwoEdgeTargetExhaustion
      (G := G) (hfree := hfree) (hv := hv) (p := p) 0 1) ∨
    Nonempty (OneHighRepeatedTwoEdgeTargetExhaustion
      (G := G) (hfree := hfree) (hv := hv) (p := p) 0 2) ∨
    Nonempty (OneHighRepeatedTwoEdgeTargetExhaustion
      (G := G) (hfree := hfree) (hv := hv) (p := p) 1 2) := by
  have hsel := oneHigh_oddProfile_graphPairing_has_repeatedTwoEdgeOwnerSelection
    G hfree hv p hprofile heven stored hstored hagree
  obtain ⟨e₀, e₁, e₂, he₀, he₁, he₂, owner, hedges, hpair⟩ :=
    oneHigh_repeatedTwoEdgeOwnerSelection_exists_pairwise_shared
      ⟨p.profile, Nat.lt_succ_iff.mpr p.profile_le⟩
      (oneHighGraphPairingRefinement G hfree hv p) hsel
  rcases hpair with h01 | h02 | h12
  · left
    exact oneHigh_pairwiseShared_exists_targetExhaustion
      (by decide) e₀.1 e₀.2 e₁.1 e₁.2 owner he₀ he₁ h01.1 h01.2 hedges
  · right; left
    exact oneHigh_pairwiseShared_exists_targetExhaustion
      (by decide) e₀.1 e₀.2 e₂.1 e₂.2 owner he₀ he₂ h02.1 h02.2 hedges
  · right; right
    exact oneHigh_pairwiseShared_exists_targetExhaustion
      (by decide) e₁.1 e₁.2 e₂.1 e₂.2 owner he₁ he₂ h12.1 h12.2 hedges

end

end Erdos85

#print axioms Erdos85.oneHigh_oddProfile_exists_repeatedTwoEdgeTargetExhaustion
