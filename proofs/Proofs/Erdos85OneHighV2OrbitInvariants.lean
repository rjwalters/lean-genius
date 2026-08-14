import Proofs.Erdos85OneHighRawPresentation
import Proofs.Erdos85BranchDeficitSymmetry

/-! # Graph-derived invariants of raw one-high orbit tables -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The directed miss matrix of a packaged one-high presentation is
symmetric.  This is the graph-side justification for storing only the
upper-triangular part of an orbit table. -/
theorem OneHighRawV2Presentation.missCount_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (p : OneHighRawV2Presentation G hfree v)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    highBranchMissCount G v s t = highBranchMissCount G v t s := by
  apply highBranchMissCount_comm_of_equal_card G hfree s t
  have hs := Fintype.card_congr (p.leafLabel s)
  have ht := Fintype.card_congr (p.leafLabel t)
  simpa using hs.trans ht.symm

/-- Every raw miss row has the profile-prescribed total.  The summation is
over the six branches other than the source and its canonical mate. -/
theorem OneHighRawV2Presentation.sum_far_missCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (s : {z : V // z ∈ G.neighborSet v}) :
    (∑ u ∈ ((Finset.univ.erase s).erase (p.mate s)),
      highBranchMissCount G v s u) =
        2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) := by
  have houter : ∀ {a : V}, a ∈ secondLayerBranch G v s →
      G.degree a = 7 := by
    intro a ha
    apply p.outer_degree
    simp only [secondLayer, Finset.mem_biUnion]
    exact ⟨s, Finset.mem_univ s, ha⟩
  have hrow := sum_far_highBranchMissCount_eq_matchedCount
    G hfree (d := 7) (by simpa using hv) p.external_empty
      s (p.mate s) (p.mate_adj s) houter
  rw [hrow]
  simpa using p.matched_count (p.branchLabel s)

end

end Erdos85
