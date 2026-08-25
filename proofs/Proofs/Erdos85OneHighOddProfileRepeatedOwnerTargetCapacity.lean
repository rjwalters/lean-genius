import Proofs.Erdos85OneHighOddProfileRepeatedOwnerDistinctKeys

/-! # Capacity of the shared repeated-owner target branch -/

namespace Erdos85

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

end Erdos85

#print axioms Erdos85.oneHigh_matchingEdgeSources_card
#print axioms Erdos85.oneHigh_matchingEdgeSources_eq_pair_of_internalEdges_eq_two
