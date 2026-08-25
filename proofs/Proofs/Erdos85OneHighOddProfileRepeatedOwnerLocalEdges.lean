import Proofs.Erdos85OneHighOddProfileRepeatedOwnerPair
import Proofs.Erdos85OneHighOddProfileCoherentLocalEdges

/-!
# Concrete local edges for selected repeated-owner witnesses

Unlike the earlier existence theorem for an arbitrary partition code, this
inversion accepts a specified owner-pair witness from the graph refinement.
It therefore preserves the exact owner labels selected by the repeated-owner
classifier, allowing two concrete escape configurations to be aligned on the
same actual branch.
-/

namespace Erdos85

/-- The complementary-partition code is insensitive to owner orientation. -/
theorem oneHighOwnerPartitionCode_comm (i j : Fin 8) :
    oneHighOwnerPartitionCode i j = oneHighOwnerPartitionCode j i := by
  decide +revert

/-- Reverse the two owner branches of a concrete local-edge witness.  This
allows a selected shared owner to be placed consistently in the target slot
before applying the escape theorem. -/
theorem OneHighPartitionLocalEdgeWitness.exists_swap
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {code : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p code) :
    ∃ q' : OneHighPartitionLocalEdgeWitness G hfree hv p code,
      q'.s = q.t ∧ q'.t = q.s := by
  have hsourceNe : q.t ≠ q.s := q.source_ne.symm
  have htargetNeMate : q.s ≠ p.mate q.t := by
    intro h
    apply q.target_ne_mate
    have hm := congrArg p.mate h
    simpa [p.mate_involutive q.t] using hm.symm
  have hcode :
      (oneHighOwnerPartitionCode (p.branchLabel q.t) (p.branchLabel q.s) ==
        code) = true := by
    rw [← oneHighOwnerPartitionCode_comm]
    exact q.code_eq
  rcases q.edge_data with ⟨key, hkeylt, hkeyNonmate, hfarS, hfarT,
    x, hx, hxkey, y, hy, hykey⟩
  let q' : OneHighPartitionLocalEdgeWitness G hfree hv p code :=
    ⟨q.t, q.s, hsourceNe, htargetNeMate, hcode,
      key, hkeylt, hkeyNonmate, hfarT, hfarS,
      y, hy, hykey, x, hx, hxkey⟩
  exact ⟨q', rfl, rfl⟩

/-- Invert one specified graph-refinement owner witness to its concrete pair
of internal matching edges, preserving both exact owner labels. -/
theorem oneHigh_graphOwnerPairWitness_to_partitionLocalEdgeWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (code : Fin 3) (i j : Fin 8)
    (howner : OneHighRefinementOwnerPairWitness
      (oneHighGraphPairingRefinement G hfree hv p) code i j) :
    ∃ q : OneHighPartitionLocalEdgeWitness G hfree hv p code,
      p.branchLabel q.s = i ∧ p.branchLabel q.t = j := by
  rcases howner with ⟨hij, hjmate, hcode, key, hkeylt, hkeyNonmate,
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

end Erdos85

#print axioms Erdos85.oneHighOwnerPartitionCode_comm
#print axioms Erdos85.OneHighPartitionLocalEdgeWitness.exists_swap
#print axioms Erdos85.oneHigh_graphOwnerPairWitness_to_partitionLocalEdgeWitness
