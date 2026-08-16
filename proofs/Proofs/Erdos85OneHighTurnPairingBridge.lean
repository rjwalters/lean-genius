import Proofs.Erdos85OneHighThreePairTurnSectorTerminal
import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85OneHighGraphPairingMultiplicity
import Proofs.Erdos85MatchingMultiplicityRelabel

/-! # Concrete turn witnesses inside graph source pairings -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Executable table signature of a saturated three-root-pair turn row.  The
source has two internal edges, lies in the fourth root-pair color, and its
entire endpoint-count row is the `AB, BC` path. -/
def oneHighTableHasSaturatedTurnRow
    (profile : Nat) (table : OneHighMissTable) : Bool :=
  decide (∃ source b a c : Fin 8,
    oneHighFamilyInternalEdges profile source = 2 ∧
    oneHighFamilyTableGet table source.val b.val = 2 ∧
    oneHighFamilyTableGet table source.val a.val = 1 ∧
    oneHighFamilyTableGet table source.val c.val = 1 ∧
    (∀ label : Fin 8,
      oneHighRootPair source ≠ oneHighRootPair label →
        oneHighFamilyTableGet table source.val label.val =
          oneHighLabelPairEndpointCount
              (oneHighCanonicalLabelPair a b) label +
            oneHighLabelPairEndpointCount
              (oneHighCanonicalLabelPair b c) label) ∧
    oneHighRootPair source ≠ oneHighRootPair a ∧
    oneHighRootPair source ≠ oneHighRootPair b ∧
    oneHighRootPair source ≠ oneHighRootPair c ∧
    oneHighRootPair a ≠ oneHighRootPair b ∧
    oneHighRootPair b ≠ oneHighRootPair c ∧
    oneHighRootPair a ≠ oneHighRootPair c)

set_option maxHeartbeats 800000 in
/-- Relevant-coordinate agreement preserves normalized table lookup between
distinct root-pair colors. -/
theorem oneHighFamilyTableGet_eq_of_relevantAgree_of_rootPair_ne
    {left right : OneHighMissTable}
    (h : OneHighTableRelevantAgree left right) {i j : Fin 8}
    (hij : oneHighRootPair i ≠ oneHighRootPair j) :
    oneHighFamilyTableGet left i.val j.val =
      oneHighFamilyTableGet right i.val j.val := by
  unfold oneHighFamilyTableGet
  apply h (min i.val j.val, max i.val j.val)
  fin_cases i <;> fin_cases j <;>
    simp [oneHighRootPair] at hij <;>
    simp_all [oneHighFamilyTablePairs]

/-- The saturated-turn signature depends only on the 24 table coordinates
read by the exact v2 generator. -/
theorem oneHighTableHasSaturatedTurnRow_of_relevantAgree
    {profile : Nat} {left right : OneHighMissTable}
    (h : OneHighTableRelevantAgree left right)
    (hleft : oneHighTableHasSaturatedTurnRow profile left = true) :
    oneHighTableHasSaturatedTurnRow profile right = true := by
  rw [oneHighTableHasSaturatedTurnRow, decide_eq_true_eq] at hleft ⊢
  rcases hleft with ⟨source, b, a, c, hedges, hb, ha, hc, hrow,
    hsa, hsb, hsc, hab, hbc, hac⟩
  refine ⟨source, b, a, c, hedges, ?_, ?_, ?_, ?_, hsa, hsb, hsc,
    hab, hbc, hac⟩
  · rw [← hb]
    exact (oneHighFamilyTableGet_eq_of_relevantAgree_of_rootPair_ne h hsb).symm
  · rw [← ha]
    exact (oneHighFamilyTableGet_eq_of_relevantAgree_of_rootPair_ne h hsa).symm
  · rw [← hc]
    exact (oneHighFamilyTableGet_eq_of_relevantAgree_of_rootPair_ne h hsc).symm
  · intro label hslabel
    rw [← hrow label hslabel]
    exact (oneHighFamilyTableGet_eq_of_relevantAgree_of_rootPair_ne h hslabel).symm

@[simp] theorem oneHighLabelPairEndpointCount_canonical_left
    {a b : Fin 8} (h : a ≠ b) :
    oneHighLabelPairEndpointCount (oneHighCanonicalLabelPair a b) a = 1 := by
  rcases lt_or_gt_of_ne h with hab | hba
  · simp [oneHighLabelPairEndpointCount, oneHighCanonicalLabelPair,
      min_eq_left hab.le, max_eq_right hab.le, h, h.symm]
  · simp [oneHighLabelPairEndpointCount, oneHighCanonicalLabelPair,
      min_eq_right hba.le, max_eq_left hba.le, h, h.symm]

@[simp] theorem oneHighLabelPairEndpointCount_canonical_right
    {a b : Fin 8} (h : a ≠ b) :
    oneHighLabelPairEndpointCount (oneHighCanonicalLabelPair a b) b = 1 := by
  rw [oneHighCanonicalLabelPair]
  rcases lt_or_gt_of_ne h with hab | hba
  · simp [oneHighLabelPairEndpointCount, min_eq_left hab.le,
      max_eq_right hab.le, h]
  · simp [oneHighLabelPairEndpointCount, min_eq_right hba.le,
      max_eq_left hba.le, h]

@[simp] theorem oneHighLabelPairEndpointCount_canonical_other
    {a b c : Fin 8} (hca : c ≠ a) (hcb : c ≠ b) :
    oneHighLabelPairEndpointCount (oneHighCanonicalLabelPair a b) c = 0 := by
  rcases le_total a b with hab | hba
  · simp [oneHighLabelPairEndpointCount, oneHighCanonicalLabelPair,
      min_eq_left hab, max_eq_right hab, hca.symm, hcb.symm]
  · simp [oneHighLabelPairEndpointCount, oneHighCanonicalLabelPair,
      min_eq_right hba, max_eq_left hba, hca.symm, hcb.symm]

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

/-- A same-owner turn forces the executable saturated-turn signature on the
relabeled graph table. -/
theorem OneHighPinnedThreePairTurn.graphRelevantMissTable_hasSaturatedTurnRow
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (howner : T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1) :
    oneHighTableHasSaturatedTurnRow p.profile
      (oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) = true := by
  rw [oneHighTableHasSaturatedTurnRow, decide_eq_true_eq]
  have hfourth := T.sharpened_source_sector G hfree hv p
  have hcolor :
      oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) =
        oneHighRootPair (p.branchLabel T.qBC.sourceEdge.1) := by
    rw [howner]
  rcases hfourth with hfourth | hc | ha
  · have hab : p.branchLabel T.a ≠ p.branchLabel T.b := fun h =>
      T.ab_pair_ne (congrArg oneHighRootPair h)
    have hbc : p.branchLabel T.b ≠ p.branchLabel T.c := fun h =>
      T.bc_pair_ne (congrArg oneHighRootPair h)
    have hac : p.branchLabel T.a ≠ p.branchLabel T.c := fun h =>
      T.ac_pair_ne (congrArg oneHighRootPair h)
    have hrow := T.sameOwner_graphRelevantMissTable_eq G hfree hv p howner
    refine ⟨p.branchLabel T.qAB.sourceEdge.1,
      p.branchLabel T.b, p.branchLabel T.a, p.branchLabel T.c,
      T.sameOwner_internalEdges_eq_two G hfree hv p howner, ?_, ?_, ?_, ?_,
      hfourth.2.1, hfourth.2.2.1, hfourth.2.2.2,
      T.ab_pair_ne, T.bc_pair_ne, T.ac_pair_ne⟩
    · rw [oneHighFamilyTableGet_graphRelevantMissTable, hrow]
      simp [hab, hbc]
    · rw [oneHighFamilyTableGet_graphRelevantMissTable, hrow]
      simp [hab, hbc, hac, hab.symm, hbc.symm, hac.symm]
    · rw [oneHighFamilyTableGet_graphRelevantMissTable, hrow]
      simp [hab, hbc, hac, hab.symm, hbc.symm, hac.symm]
    · intro label _
      rw [oneHighFamilyTableGet_graphRelevantMissTable]
      exact hrow label
  · exact False.elim ((oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
      p.branch_mate T.qBC.sourceEdge.1 T.c T.qBC.right_far)
        (hcolor.symm.trans hc))
  · exact False.elim ((oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
      p.branch_mate T.qAB.sourceEdge.1 T.a T.qAB.left_far)
        (hcolor.trans ha))

/-- For every pinned turn, either one witnessed owner row is completely
reconstructed as its singleton key, or both owner rows are saturated
two-entry rows.  This covers all six literal owner branches uniformly. -/
theorem OneHighPinnedThreePairTurn.sourcePairing_singleton_or_both_saturated
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p) :
    oneHighGraphSourcePairing G hfree hv p
        (p.branchLabel T.qAB.sourceEdge.1) =
        [oneHighCanonicalLabelPair (p.branchLabel T.a) (p.branchLabel T.b)] ∨
      oneHighGraphSourcePairing G hfree hv p
        (p.branchLabel T.qBC.sourceEdge.1) =
        [oneHighCanonicalLabelPair (p.branchLabel T.b) (p.branchLabel T.c)] ∨
      ((oneHighGraphSourcePairing G hfree hv p
          (p.branchLabel T.qAB.sourceEdge.1)).length = 2 ∧
        (oneHighGraphSourcePairing G hfree hv p
          (p.branchLabel T.qBC.sourceEdge.1)).length = 2) := by
  let rowAB := oneHighGraphSourcePairing G hfree hv p
    (p.branchLabel T.qAB.sourceEdge.1)
  let rowBC := oneHighGraphSourcePairing G hfree hv p
    (p.branchLabel T.qBC.sourceEdge.1)
  let pairAB := oneHighCanonicalLabelPair
    (p.branchLabel T.a) (p.branchLabel T.b)
  let pairBC := oneHighCanonicalLabelPair
    (p.branchLabel T.b) (p.branchLabel T.c)
  have hAB : pairAB ∈ rowAB :=
    T.qAB.canonicalPair_mem_graphSourcePairing G hfree hv p
  have hBC : pairBC ∈ rowBC :=
    T.qBC.canonicalPair_mem_graphSourcePairing G hfree hv p
  have hedgeAB : oneHighFamilyInternalEdges p.profile
      (p.branchLabel T.qAB.sourceEdge.1) = 1 ∨
      oneHighFamilyInternalEdges p.profile
        (p.branchLabel T.qAB.sourceEdge.1) = 2 := by
    unfold oneHighFamilyInternalEdges
    split <;> simp
  have hedgeBC : oneHighFamilyInternalEdges p.profile
      (p.branchLabel T.qBC.sourceEdge.1) = 1 ∨
      oneHighFamilyInternalEdges p.profile
        (p.branchLabel T.qBC.sourceEdge.1) = 2 := by
    unfold oneHighFamilyInternalEdges
    split <;> simp
  rcases hedgeAB with hedgeAB | hedgeAB
  · left
    have hlen : rowAB.length = 1 := by
      simpa [rowAB] using (oneHighGraphSourcePairing_length
        G hfree hv p (p.branchLabel T.qAB.sourceEdge.1)).trans hedgeAB
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    change rowAB = [pairAB]
    rw [hx] at hAB ⊢
    have heq : pairAB = x := by simpa using hAB
    simpa [heq]
  · rcases hedgeBC with hedgeBC | hedgeBC
    · right; left
      have hlen : rowBC.length = 1 := by
        simpa [rowBC] using (oneHighGraphSourcePairing_length
          G hfree hv p (p.branchLabel T.qBC.sourceEdge.1)).trans hedgeBC
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
      change rowBC = [pairBC]
      rw [hx] at hBC ⊢
      have heq : pairBC = x := by simpa using hBC
      simpa [heq]
    · right; right
      constructor
      · simpa [rowAB] using (oneHighGraphSourcePairing_length
          G hfree hv p (p.branchLabel T.qAB.sourceEdge.1)).trans hedgeAB
      · simpa [rowBC] using (oneHighGraphSourcePairing_length
          G hfree hv p (p.branchLabel T.qBC.sourceEdge.1)).trans hedgeBC

/-- The pinned `AB` edge remains odd in the concrete graph-induced global
pairing refinement. -/
theorem OneHighPinnedThreePairTurn.graphPairingMultiplicity_ab_odd
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p) :
    Odd (oneHighPairingRefinementMultiplicity
      (oneHighGraphPairingRefinement G hfree hv p)
      (oneHighCanonicalLabelPair (p.branchLabel T.a) (p.branchLabel T.b))) := by
  have hab : p.branchLabel T.a ≠ p.branchLabel T.b := fun h =>
    T.ab_pair_ne (congrArg oneHighRootPair h)
  rw [oneHighGraphPairingRefinementMultiplicity_eq_global G hfree hv p _
    (min_lt_max.mpr hab)]
  exact T.ab_odd

/-- The pinned `BC` edge remains odd in the concrete graph-induced global
pairing refinement. -/
theorem OneHighPinnedThreePairTurn.graphPairingMultiplicity_bc_odd
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p) :
    Odd (oneHighPairingRefinementMultiplicity
      (oneHighGraphPairingRefinement G hfree hv p)
      (oneHighCanonicalLabelPair (p.branchLabel T.b) (p.branchLabel T.c))) := by
  have hbc : p.branchLabel T.b ≠ p.branchLabel T.c := fun h =>
    T.bc_pair_ne (congrArg oneHighRootPair h)
  rw [oneHighGraphPairingRefinementMultiplicity_eq_global G hfree hv p _
    (min_lt_max.mpr hbc)]
  exact T.bc_odd

end

end Erdos85
