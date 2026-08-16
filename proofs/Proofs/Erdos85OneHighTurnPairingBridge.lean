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

/-- In the same-owner sector, the two witnessed keys exhaust the saturated
two-entry source pairing row. -/
theorem OneHighPinnedThreePairTurn.sameOwner_sourcePairing_perm
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1) :
    (oneHighGraphSourcePairing G hfree hv p
      (p.branchLabel T.qAB.sourceEdge.1)).Perm
        [oneHighCanonicalLabelPair (p.branchLabel T.a) (p.branchLabel T.b),
          oneHighCanonicalLabelPair (p.branchLabel T.b) (p.branchLabel T.c)] := by
  let pairAB := oneHighCanonicalLabelPair
    (p.branchLabel T.a) (p.branchLabel T.b)
  let pairBC := oneHighCanonicalLabelPair
    (p.branchLabel T.b) (p.branchLabel T.c)
  let row := oneHighGraphSourcePairing G hfree hv p
    (p.branchLabel T.qAB.sourceEdge.1)
  have hpairNe : pairAB ≠ pairBC := by
    intro h
    have hp := (canonicalOrderedPair_eq_iff
      (p.branchLabel T.a) (p.branchLabel T.b)
      (p.branchLabel T.b) (p.branchLabel T.c)).mp h
    rcases hp with hp | hp
    · exact T.ab_pair_ne (congrArg oneHighRootPair hp.1)
    · exact T.ac_pair_ne (congrArg oneHighRootPair hp.1)
  have hAB : pairAB ∈ row := by
    exact T.qAB.canonicalPair_mem_graphSourcePairing G hfree hv p
  have hBC : pairBC ∈ row := by
    have := T.qBC.canonicalPair_mem_graphSourcePairing G hfree hv p
    simpa [row, howner] using this
  have hlen : row.length = 2 := by
    change (oneHighGraphSourcePairing G hfree hv p
      (p.branchLabel T.qAB.sourceEdge.1)).length = 2
    rw [oneHighGraphSourcePairing_length,
      T.sameOwner_internalEdges_eq_two G hfree hv p howner]
  obtain ⟨u, w, hrow⟩ := List.length_eq_two.mp hlen
  change row.Perm [pairAB, pairBC]
  rw [hrow] at hAB hBC ⊢
  simp at hAB hBC
  rcases hAB with hAB | hAB <;> rcases hBC with hBC | hBC
  · exact (hpairNe (hAB.trans hBC.symm)).elim
  · subst u; subst w; simp
  · subst u; subst w; exact List.Perm.swap _ _ []
  · exact (hpairNe (hAB.trans hBC.symm)).elim

/-- The exact graph-table row forced by a same-owner turn: its endpoint-count
function is the sum of the two witnessed `AB` and `BC` keys. -/
theorem OneHighPinnedThreePairTurn.sameOwner_graphRelevantMissTable_eq
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1) (label : Fin 8) :
    oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile (p.branchLabel T.qAB.sourceEdge.1).val label.val =
      oneHighLabelPairEndpointCount
          (oneHighCanonicalLabelPair (p.branchLabel T.a) (p.branchLabel T.b)) label +
        oneHighLabelPairEndpointCount
          (oneHighCanonicalLabelPair (p.branchLabel T.b) (p.branchLabel T.c)) label := by
  rw [← oneHighGraphSourcePairing_endpointCount G hfree hv p]
  have hp := (T.sameOwner_sourcePairing_perm G hfree hv p howner).map
    (fun pair => oneHighLabelPairEndpointCount pair label)
  rw [oneHighPairingEndpointCount, hp.sum_eq]
  simp

end

end Erdos85
