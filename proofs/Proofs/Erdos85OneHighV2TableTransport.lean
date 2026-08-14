import Proofs.Erdos85OneHighV2GraphLedgers

/-!
# Coordinate transport for the v2 graph miss table

The encoded full miss deficit over a branch block equals the raw
graph-side `highBranchMissCount`, transported through the canonical
leaf labeling.  Composed with the worker-count/full-deficit bridge
this pins `oneHighFamilyGraphTable` to graph miss counts.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Membership in a branch transports to the encoded block. -/
theorem oneHighLeafFinFortyEquiv_mem_blockFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s : {z : V // z ∈ G.neighborSet v})
    (x : {z : V // z ∈ secondLayer G v}) :
    oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel x ∈
        oneHighFamilyBlockFinset (branchLabel s) ↔
      oneHighBranchOwner G v x = s := by
  constructor
  · intro hx
    have hdiv := (Finset.mem_filter.mp hx).2
    rw [oneHighLeafFinFortyEquiv_divNat] at hdiv
    exact branchLabel.injective hdiv
  · intro howner
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [oneHighLeafFinFortyEquiv_divNat, howner]

/-- The encoded full miss deficit over the block of `s` toward the
block of `u` equals `highBranchMissCount G v s u`. -/
theorem oneHighFamilyEncodedFullDeficit_eq_highBranchMissCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (leafLabel : ∀ s : {z : V // z ∈ G.neighborSet v},
      secondLayerBranch G v s ≃ Fin 5)
    (s u : {z : V // z ∈ G.neighborSet v}) :
    let E := oneHighLeafFinFortyEquiv G hfree v branchLabel leafLabel
    let R := oneHighRelabeledLeafGraph G v E
    ((oneHighFamilyBlockFinset (branchLabel s)).filter fun x =>
      (R.neighborFinset x ∩
        oneHighFamilyBlockFinset (branchLabel u)).card = 0).card =
      highBranchMissCount G v s u := by
  intro E R
  classical
  unfold highBranchMissCount
  -- neighborhood correspondence for one encoded leaf
  have hnbhd : ∀ x : {z : V // z ∈ secondLayer G v},
      ((R.neighborFinset (E x) ∩
        oneHighFamilyBlockFinset (branchLabel u)).card = 0) ↔
      ((G.neighborFinset x.val ∩ secondLayerBranch G v u).card = 0) := by
    intro x
    rw [Finset.card_eq_zero, Finset.card_eq_zero]
    constructor
    · intro h
      apply Finset.eq_empty_of_forall_notMem
      intro a ha
      have haParts := Finset.mem_inter.mp ha
      have haAdj := (G.mem_neighborFinset _ _).mp haParts.1
      have haBranch := haParts.2
      have haSecond : a ∈ secondLayer G v := by
        unfold secondLayer
        exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ u, haBranch⟩
      have hz : E ⟨a, haSecond⟩ ∈
          R.neighborFinset (E x) ∩
            oneHighFamilyBlockFinset (branchLabel u) := by
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · apply (R.mem_neighborFinset _ _).mpr
          show (squareOrderOuterGraph G v).Adj
            (E.symm (E x)) (E.symm (E ⟨a, haSecond⟩))
          rw [E.symm_apply_apply, E.symm_apply_apply]
          exact haAdj
        · exact (oneHighLeafFinFortyEquiv_mem_blockFinset_iff
            G hfree v branchLabel leafLabel u ⟨a, haSecond⟩).mpr
            (oneHighBranchOwner_eq_of_mem G hfree v ⟨a, haSecond⟩ u haBranch)
      rw [h] at hz
      simp at hz
    · intro h
      apply Finset.eq_empty_of_forall_notMem
      intro z hz
      have hzParts := Finset.mem_inter.mp hz
      have hzAdj : (squareOrderOuterGraph G v).Adj
          (E.symm (E x)) (E.symm z) :=
        (R.mem_neighborFinset _ _).mp hzParts.1
      rw [E.symm_apply_apply] at hzAdj
      have hzOwner : oneHighBranchOwner G v (E.symm z) = u := by
        have := hzParts.2
        rw [show z = E (E.symm z) from (E.apply_symm_apply z).symm] at this
        exact (oneHighLeafFinFortyEquiv_mem_blockFinset_iff
          G hfree v branchLabel leafLabel u (E.symm z)).mp this
      have hmem : (E.symm z).val ∈
          G.neighborFinset x.val ∩ secondLayerBranch G v u := by
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · exact (G.mem_neighborFinset _ _).mpr hzAdj
        · rw [← hzOwner]
          exact oneHighBranchOwner_mem G v (E.symm z)
      rw [h] at hmem
      simp at hmem
  -- the block filter bijects with the branch filter
  apply Finset.card_bij (fun x _ => (E.symm x).val)
  · intro x hx
    have hxParts := Finset.mem_filter.mp hx
    have hxOwner : oneHighBranchOwner G v (E.symm x) = s := by
      have := hxParts.1
      rw [show x = E (E.symm x) from (E.apply_symm_apply x).symm] at this
      exact (oneHighLeafFinFortyEquiv_mem_blockFinset_iff
        G hfree v branchLabel leafLabel s (E.symm x)).mp this
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hxOwner]
      exact oneHighBranchOwner_mem G v (E.symm x)
    · have := hxParts.2
      rw [show x = E (E.symm x) from (E.apply_symm_apply x).symm] at this
      exact (hnbhd (E.symm x)).mp this
  · intro x hx y hy heq
    have : (E.symm x) = (E.symm y) := Subtype.ext heq
    exact E.symm.injective this
  · intro a ha
    have haParts := Finset.mem_filter.mp ha
    have haSecond : a ∈ secondLayer G v := by
      unfold secondLayer
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s, haParts.1⟩
    refine ⟨E ⟨a, haSecond⟩, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact (oneHighLeafFinFortyEquiv_mem_blockFinset_iff
          G hfree v branchLabel leafLabel s ⟨a, haSecond⟩).mpr
          (oneHighBranchOwner_eq_of_mem G hfree v ⟨a, haSecond⟩ s haParts.1)
      · exact (hnbhd ⟨a, haSecond⟩).mpr haParts.2
    · simp [E.symm_apply_apply]

end

end Erdos85
