import Proofs.Erdos85OneHighOddProfileCoherentLocalEdges
import Proofs.Erdos85OneHighOddProfileRepeatedOwnerPair

/-! # Preserve a repeated selected owner through graph-edge inversion -/

namespace Erdos85

/-- Invert a specified refinement-level owner witness, rather than choosing
a fresh witness for the same partition code.  The returned label equalities
are what allow finite repeated-owner coherence to survive graph transport. -/
theorem oneHigh_partitionLocalEdgeWitness_of_ownerPairWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (code : Fin 3) (i j : Fin 8)
    (hw : OneHighRefinementOwnerPairWitness
      (oneHighGraphPairingRefinement G hfree hv p) code i j) :
    ∃ q : OneHighPartitionLocalEdgeWitness G hfree hv p code,
      p.branchLabel q.s = i ∧ p.branchLabel q.t = j := by
  rcases hw with ⟨hij, hjmate, hcode, key, hkeylt, hkeyNonmate,
    hkeyFarI, hkeyFarJ, hkeyi, hkeyj⟩
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
  let q : OneHighPartitionLocalEdgeWitness G hfree hv p code :=
    ⟨s, t, hst, htMate, hcodeST, key, hkeylt, hkeyNonmate,
      hkeyFarS, hkeyFarT, x, hx, hxkey, y, hy, hykey⟩
  exact ⟨q, by simp [q, s], by simp [q, t]⟩

/-- The classified repeated-owner selection yields three concrete local-edge
witnesses, one per partition, with an exact graph branch shared by a
specified pair of witnesses. -/
theorem oneHigh_oddProfile_exists_partitionLocalEdges_with_repeatedOwner
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
    ∃ q₀ : OneHighPartitionLocalEdgeWitness G hfree hv p 0,
      ∃ q₁ : OneHighPartitionLocalEdgeWitness G hfree hv p 1,
        ∃ q₂ : OneHighPartitionLocalEdgeWitness G hfree hv p 2,
          ∃ z : {x : V // x ∈ G.neighborSet v},
            (z ∈ ({q₀.s, q₀.t} : Finset _) ∧
              z ∈ ({q₁.s, q₁.t} : Finset _)) ∨
            (z ∈ ({q₀.s, q₀.t} : Finset _) ∧
              z ∈ ({q₂.s, q₂.t} : Finset _)) ∨
            (z ∈ ({q₁.s, q₁.t} : Finset _) ∧
              z ∈ ({q₂.s, q₂.t} : Finset _)) := by
  have hsel := oneHigh_oddProfile_graphPairing_has_repeatedOwnerSelection
    G hfree hv p hprofile heven stored hstored hagree
  obtain ⟨e₀, e₁, e₂, hw₀, hw₁, hw₂, label, hshared⟩ :=
    oneHigh_repeatedOwnerSelection_exists_pairwise_shared _ hsel
  obtain ⟨q₀, hq₀s, hq₀t⟩ :=
    oneHigh_partitionLocalEdgeWitness_of_ownerPairWitness
      G hfree hv p 0 e₀.1 e₀.2 hw₀
  obtain ⟨q₁, hq₁s, hq₁t⟩ :=
    oneHigh_partitionLocalEdgeWitness_of_ownerPairWitness
      G hfree hv p 1 e₁.1 e₁.2 hw₁
  obtain ⟨q₂, hq₂s, hq₂t⟩ :=
    oneHigh_partitionLocalEdgeWitness_of_ownerPairWitness
      G hfree hv p 2 e₂.1 e₂.2 hw₂
  let z := p.branchLabel.symm label
  refine ⟨q₀, q₁, q₂, z, ?_⟩
  have hmem₀ : label ∈ ({e₀.1, e₀.2} : Finset (Fin 8)) →
      z ∈ ({q₀.s, q₀.t} : Finset _) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h
    · left; apply p.branchLabel.injective; simpa [z, hq₀s] using h
    · right; apply p.branchLabel.injective; simpa [z, hq₀t] using h
  have hmem₁ : label ∈ ({e₁.1, e₁.2} : Finset (Fin 8)) →
      z ∈ ({q₁.s, q₁.t} : Finset _) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h
    · left; apply p.branchLabel.injective; simpa [z, hq₁s] using h
    · right; apply p.branchLabel.injective; simpa [z, hq₁t] using h
  have hmem₂ : label ∈ ({e₂.1, e₂.2} : Finset (Fin 8)) →
      z ∈ ({q₂.s, q₂.t} : Finset _) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h
    · left; apply p.branchLabel.injective; simpa [z, hq₂s] using h
    · right; apply p.branchLabel.injective; simpa [z, hq₂t] using h
  rcases hshared with h01 | h02 | h12
  · exact Or.inl ⟨hmem₀ h01.1, hmem₁ h01.2⟩
  · exact Or.inr (Or.inl ⟨hmem₀ h02.1, hmem₂ h02.2⟩)
  · exact Or.inr (Or.inr ⟨hmem₁ h12.1, hmem₂ h12.2⟩)

end Erdos85

#print axioms Erdos85.oneHigh_partitionLocalEdgeWitness_of_ownerPairWitness
#print axioms Erdos85.oneHigh_oddProfile_exists_partitionLocalEdges_with_repeatedOwner
