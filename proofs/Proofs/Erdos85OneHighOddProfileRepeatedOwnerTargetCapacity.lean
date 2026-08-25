import Proofs.Erdos85OneHighOddProfileRepeatedOwnerDistinctKeys

/-! # Capacity of the shared repeated-owner target branch -/

namespace Erdos85

/-- Transport a matched branch vertex across equality of its branch index. -/
def oneHighMatchedBranchTransport
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    {s t : {x : V // x ∈ G.neighborSet v}} (h : s = t)
    (x : OneHighMatchedBranchVertices G v s) :
    OneHighMatchedBranchVertices G v t := h ▸ x

/-- The canonical miss-label key carried by one internal matching edge. -/
noncomputable def oneHighTargetMissKey
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (s : {x : V // x ∈ G.neighborSet v})
    (x : OneHighMatchedBranchVertices G v s) : OneHighLabelPair :=
  (min
      (p.branchLabel (oneHighMatchedMissLabel G hfree hv
        p.external_empty p.outer_degree p.mate p.mate_adj s x))
      (p.branchLabel (oneHighMatchedMissLabel G hfree hv
        p.external_empty p.outer_degree p.mate p.mate_adj s
          (oneHighInternalMate G hfree v s x))),
    max
      (p.branchLabel (oneHighMatchedMissLabel G hfree hv
        p.external_empty p.outer_degree p.mate p.mate_adj s x))
      (p.branchLabel (oneHighMatchedMissLabel G hfree hv
        p.external_empty p.outer_degree p.mate p.mate_adj s
          (oneHighInternalMate G hfree v s x))))

@[simp] theorem oneHighTargetMissKey_transport
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    {s t : {x : V // x ∈ G.neighborSet v}} (h : s = t)
    (x : OneHighMatchedBranchVertices G v s) :
    oneHighTargetMissKey G hfree hv p t
        (oneHighMatchedBranchTransport G v h x) =
      oneHighTargetMissKey G hfree hv p s x := by
  subst t
  rfl

theorem oneHighMatchedBranchTransport_mem_matchingEdgeSources
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    {s t : {x : V // x ∈ G.neighborSet v}} (h : s = t)
    (x : OneHighMatchedBranchVertices G v s)
    (hx : x ∈ matchingEdgeSources (oneHighInternalMate G hfree v s)) :
    oneHighMatchedBranchTransport G v h x ∈
      matchingEdgeSources (oneHighInternalMate G hfree v t) := by
  subst t
  exact hx

/-- The canonical internal-edge source finset of an actual branch has exactly
the number of edges prescribed by that branch's one-high profile label. -/
theorem oneHigh_matchingEdgeSources_card
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v)
    (s : {x : V // x ∈ G.neighborSet v}) :
    (matchingEdgeSources (oneHighInternalMate G hfree v s)).card =
      oneHighFamilyInternalEdges p.profile (p.branchLabel s) := by
  have hinv : Function.Involutive (oneHighInternalMate G hfree v s) := by
    simpa [oneHighInternalMate] using degreeOneMate_involutive
      (G.induce (secondLayerBranch G v s))
      (degree_induce_secondLayerBranch_le_one G hfree v s)
  have hne : ∀ x, oneHighInternalMate G hfree v s x ≠ x := by
    simpa [oneHighInternalMate] using degreeOneMate_ne
      (G.induce (secondLayerBranch G v s))
      (degree_induce_secondLayerBranch_le_one G hfree v s)
  have htwice := two_mul_matchingEdgeSources_card
    (oneHighInternalMate G hfree v s) hinv hne
  have hcard : Fintype.card (OneHighMatchedBranchVertices G v s) =
      2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) := by
    calc
      Fintype.card (OneHighMatchedBranchVertices G v s) =
          highBranchMatchedCount G v s :=
        card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount G v s
      _ = 2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) := by
        simpa using p.matched_count (p.branchLabel s)
  omega

/-- In a two-edge branch, any two distinct canonical matching-edge sources
exhaust the entire internal matching. -/
theorem oneHigh_matchingEdgeSources_eq_pair_of_internalEdges_eq_two
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v)
    (s : {x : V // x ∈ G.neighborSet v})
    (hedges : oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 2)
    (x y : OneHighMatchedBranchVertices G v s)
    (hx : x ∈ matchingEdgeSources (oneHighInternalMate G hfree v s))
    (hy : y ∈ matchingEdgeSources (oneHighInternalMate G hfree v s))
    (hxy : x ≠ y) :
    matchingEdgeSources (oneHighInternalMate G hfree v s) = {x, y} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · simpa using Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
  · rw [oneHigh_matchingEdgeSources_card G hfree p s, hedges]
    simp [hxy]

/-- For unequal partition codes oriented at one branch, transport both
distinguished target edges into the same branch type; their canonical sources
are distinct because their exact miss-label keys are distinct. -/
theorem oneHigh_orientedDistinctCodes_exists_distinctTargetSources
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v} {c d : Fin 3}
    (q : OneHighPartitionLocalEdgeWitness G hfree hv p c)
    (r : OneHighPartitionLocalEdgeWitness G hfree hv p d)
    (htarget : q.t = r.t) (hcode : c ≠ d) :
    ∃ yq yr : OneHighMatchedBranchVertices G v q.t,
      yq ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t) ∧
      yr ∈ matchingEdgeSources (oneHighInternalMate G hfree v q.t) ∧
      yq ≠ yr := by
  obtain ⟨keyq, keyr, hkeys, ⟨yq, hyq, hyqKey⟩,
    ⟨yr, hyr, hyrKey⟩⟩ :=
    oneHigh_orientedSharedOwner_unequalCodes_targetKeys_ne
      q r htarget hcode
  let yrq := oneHighMatchedBranchTransport G v htarget.symm yr
  have hyrq : yrq ∈
      matchingEdgeSources (oneHighInternalMate G hfree v q.t) :=
    oneHighMatchedBranchTransport_mem_matchingEdgeSources
      G hfree htarget.symm yr hyr
  have hyqKey' : oneHighTargetMissKey G hfree hv p q.t yq = keyq := by
    exact hyqKey
  have hyrKey' : oneHighTargetMissKey G hfree hv p r.t yr = keyr := by
    exact hyrKey
  refine ⟨yq, yrq, hyq, hyrq, ?_⟩
  intro heq
  apply hkeys
  rw [← hyqKey', ← hyrKey']
  rw [← oneHighTargetMissKey_transport G hfree hv p htarget.symm yr]
  exact congrArg (oneHighTargetMissKey G hfree hv p q.t) heq

end Erdos85

#print axioms Erdos85.oneHigh_matchingEdgeSources_card
#print axioms Erdos85.oneHigh_matchingEdgeSources_eq_pair_of_internalEdges_eq_two
#print axioms Erdos85.oneHigh_orientedDistinctCodes_exists_distinctTargetSources
