import Proofs.Erdos85OneHighThreePairTurnSectorTerminal
import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85MatchingMultiplicityRelabel

/-! # Concrete turn witnesses inside graph source pairings -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A concrete odd-label edge witness occurs in the canonical pairing row of
its actual source branch, after transporting its two root labels through the
presentation's branch equivalence. -/
theorem OneHighOddLabelEdgeSourceWitness.canonicalPair_mem_graphSourcePairing
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    {a b : {z : V // z ∈ G.neighborSet v}}
    (q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
      p.outer_degree p.mate p.mate_adj a b) :
    oneHighCanonicalLabelPair (p.branchLabel a) (p.branchLabel b) ∈
      oneHighGraphSourcePairing G hfree hv p
        (p.branchLabel q.sourceEdge.1) := by
  let s := q.sourceEdge.1
  let x := q.sourceEdge.2
  let M := oneHighInternalMate G hfree v s
  let rootLabel := oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s
  let label := fun z => p.branchLabel (rootLabel z)
  have hMInv : Function.Involutive M := degreeOneMate_involutive _ _
  have hMNe : M x ≠ x := degreeOneMate_ne _ _ x
  have hraw :
      (min (rootLabel x) (rootLabel (M x)),
        max (rootLabel x) (rootLabel (M x))) = (min a b, max a b) := by
    simpa [s, x, M, rootLabel, exchangedMissPairKey,
      oneHighGlobalInternalMate, oneHighGlobalMissLabel] using q.key_eq
  have hpair :
      (min (label x) (label (M x)), max (label x) (label (M x))) =
        oneHighCanonicalLabelPair (p.branchLabel a) (p.branchLabel b) := by
    exact (canonicalOrderedPair_equiv_eq_iff p.branchLabel
      (rootLabel x) (rootLabel (M x)) a b).2 hraw
  have hlocal : oneHighCanonicalLabelPair
      (p.branchLabel a) (p.branchLabel b) ∈
      matchingPairingListSorted M label := by
    rcases lt_or_gt_of_ne hMNe with hlt | hgt
    · have hm : M x ∈ matchingEdgeSources M := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [hMInv x] using hlt
      have hmem := canonicalPair_mem_matchingPairingListSorted_of_mem_source
        M label hm
      simpa [hMInv x, min_comm, max_comm, hpair] using hmem
    · rw [← hpair]
      apply canonicalPair_mem_matchingPairingListSorted_of_mem_source
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩
  rw [oneHighGraphSourcePairing, p.branchLabel.symm_apply_apply]
  simpa [s, M, label, rootLabel] using hlocal

end

end Erdos85
