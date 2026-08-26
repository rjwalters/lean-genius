import Proofs.Erdos85OneHighGraphCanonicalSlotRefinement
import Proofs.Erdos85MatchingPairingDuplicateKey

/-! # Equal-key two-edge canonical slot rows -/

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
theorem oneHighGraphCanonicalSlotRow_mem_variants_of_two_equal
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (source : Fin 8)
    (htwo : oneHighFamilyInternalEdges p.profile source = 2)
    (hequal :
      (oneHighGraphCanonicalSlotLabel G hfree p source 0,
        oneHighGraphCanonicalSlotLabel G hfree p source 1) =
      (oneHighGraphCanonicalSlotLabel G hfree p source 2,
        oneHighGraphCanonicalSlotLabel G hfree p source 3)) :
    oneHighGraphCanonicalSlotRow G hfree p source ∈
      oneHighPairingRowSlotVariants
        (oneHighGraphSourcePairing G hfree hv p source) := by
  let s := p.branchLabel.symm source
  let H := G.induce (secondLayerBranch G v s)
  let M := oneHighInternalMate G hfree v s
  let rootLabel := oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s
  let label := fun z => p.branchLabel (rootLabel z)
  have hmatched (offset : Fin 5) (hoff : offset.val < 4) :
      oneHighFamilyVertexMatched p.profile
        (oneHighFamilyVertex source offset).val = true := by
    simp [oneHighFamilyVertexMatched, oneHighFamilyVertex_val]
    unfold oneHighFamilyInternalEdges at htwo
    split at htwo
    · omega
    · omega
  let loc (offset : Fin 5) := (p.leafLabel s).symm offset
  have hdegree (offset : Fin 5) (hoff : offset.val < 4) :
      H.degree (loc offset) = 1 := by
    rw [degree_induce_secondLayerBranch_eq_card_inter]
    simpa [H, s, loc] using card_oneHighCanonicalSlot_internal_eq_one
      G hfree p source offset (hmatched offset hoff)
  let matched (offset : Fin 5) (hoff : offset.val < 4) :
      OneHighMatchedBranchVertices G v s :=
    ⟨loc offset, hdegree offset hoff⟩
  have hmate (left right : Fin 5)
      (hleft : left.val < 4) (hright : right.val < 4)
      (hadjR : (oneHighRelabeledLeafGraph G v
        (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)).Adj
          (oneHighFamilyVertex source left)
          (oneHighFamilyVertex source right)) :
      M (matched left hleft) = matched right hright := by
    apply Subtype.ext
    have hdecodeLeft := oneHighLeafFinFortyEquiv_symm_familyVertex
      G hfree p.branchLabel p.leafLabel s left
    have hdecodeRight := oneHighLeafFinFortyEquiv_symm_familyVertex
      G hfree p.branchLabel p.leafLabel s right
    have hadjG : G.Adj (loc left).1 (loc right).1 := by
      have h := (oneHighRelabeledLeafGraph_adj G v
        (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel) _ _).mp
          hadjR
      have hs : p.branchLabel s = source := p.branchLabel.apply_symm_apply source
      rw [hs] at hdecodeLeft hdecodeRight
      rw [hdecodeLeft, hdecodeRight] at h
      exact h
    have hMmem : (M (matched left hleft)).1 ∈
        H.neighborFinset (matched left hleft).1 :=
      (H.mem_neighborFinset _ _).mpr (by
        simpa [M, oneHighInternalMate, H] using degreeOneMate_adj H
          (degree_induce_secondLayerBranch_le_one G hfree v s)
          (matched left hleft))
    have hrymem : (matched right hright).1 ∈
        H.neighborFinset (matched left hleft).1 :=
      (H.mem_neighborFinset _ _).mpr (by
        simpa [H, matched, loc] using hadjG)
    have hone : (H.neighborFinset (matched left hleft).1).card = 1 := by
      simpa [H.card_neighborFinset_eq_degree] using
        (matched left hleft).2
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hone
    rw [hz] at hMmem hrymem
    have hMz : (M (matched left hleft)).1 = z := by simpa using hMmem
    have hryz : (matched right hright).1 = z := by simpa using hrymem
    exact hMz.trans hryz.symm
  have hadj01 : (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)).Adj
        (oneHighFamilyVertex source 0) (oneHighFamilyVertex source 1) := by
    apply of_decide_eq_true
    rw [p.constraints.relation.1 _ _ (by simp)]
    simp [oneHighCanonicalBranchAdj]
  have hcond : source.val % 2 = 1 ∨ p.profile ≤ source.val / 2 := by
    unfold oneHighFamilyInternalEdges at htwo
    split at htwo
    · omega
    · have hmod := Nat.mod_lt source.val (by omega : 0 < 2)
      omega
  have hflag : oneHighFamilyTwoEdges p.profile source = true := by
    simp [oneHighFamilyTwoEdges, hcond]
  have hadj23 : (oneHighRelabeledLeafGraph G v
      (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel)).Adj
        (oneHighFamilyVertex source 2) (oneHighFamilyVertex source 3) := by
    apply of_decide_eq_true
    rw [p.constraints.relation.1 _ _ (by simp)]
    simp [oneHighCanonicalBranchAdj, hflag]
  let x0 := matched 0 (by decide)
  let x1 := matched 1 (by decide)
  let x2 := matched 2 (by decide)
  let x3 := matched 3 (by decide)
  have hM01 : M x0 = x1 := by
    simpa [x0, x1] using hmate 0 1 (by decide) (by decide) hadj01
  have hM23 : M x2 = x3 := by
    simpa [x2, x3] using hmate 2 3 (by decide) (by decide) hadj23
  let sx := matchingEdgeSource M x0
  let sy := matchingEdgeSource M x2
  have hMInv : Function.Involutive M := degreeOneMate_involutive _ _
  have hMFree : ∀ x, M x ≠ x := degreeOneMate_ne _ _
  have hsx : sx ∈ matchingEdgeSources M :=
    matchingEdgeSource_mem M hMInv hMFree x0
  have hsy : sy ∈ matchingEdgeSources M :=
    matchingEdgeSource_mem M hMInv hMFree x2
  have hoffsetNe (i j : Fin 5) (hij : i ≠ j)
      (hi : i.val < 4) (hj : j.val < 4) :
      matched i hi ≠ matched j hj := by
    intro h
    have hlocal : loc i = loc j := congrArg Subtype.val h
    have := (p.leafLabel s).symm.injective hlocal
    exact hij this
  have hsxy : sx ≠ sy := by
    apply matchingEdgeSource_ne_of_orbits_disjoint M x0 x2
    · exact hoffsetNe 0 2 (by decide) (by decide) (by decide)
    · rw [hM01]
      exact hoffsetNe 1 2 (by decide) (by decide) (by decide)
    · rw [hM23]
      exact hoffsetNe 0 3 (by decide) (by decide) (by decide)
    · rw [hM01, hM23]
      exact hoffsetNe 1 3 (by decide) (by decide) (by decide)
  let key : OneHighLabelPair :=
    (oneHighGraphCanonicalSlotLabel G hfree p source 0,
      oneHighGraphCanonicalSlotLabel G hfree p source 1)
  have hlabel0 : label x0 = key.1 := by rfl
  have hlabel1 : label x1 = key.2 := by rfl
  have hkeyx : (min (label sx) (label (M sx)),
      max (label sx) (label (M sx))) = key := by
    rw [matchingEdgeSource_canonicalPair M hMInv label x0, hM01,
      hlabel0, hlabel1]
    exact Prod.ext
      (min_eq_left (oneHighGraphCanonicalSlotLabel_zero_le_one
        G hfree hv p source))
      (max_eq_right (oneHighGraphCanonicalSlotLabel_zero_le_one
        G hfree hv p source))
  have hkeyy : (min (label sy) (label (M sy)),
      max (label sy) (label (M sy))) = key := by
    rw [matchingEdgeSource_canonicalPair M hMInv label x2, hM23]
    have hlabel2 : label x2 =
        oneHighGraphCanonicalSlotLabel G hfree p source 2 := by rfl
    have hlabel3 : label x3 =
        oneHighGraphCanonicalSlotLabel G hfree p source 3 := by rfl
    rw [hlabel2, hlabel3,
      min_eq_left (oneHighGraphCanonicalSlotLabel_two_le_three
        G hfree hv p source htwo),
      max_eq_right (oneHighGraphCanonicalSlotLabel_two_le_three
        G hfree hv p source htwo)]
    exact hequal.symm
  have hcard : (matchingEdgeSources M).card = 2 := by
    have hlen := oneHighGraphSourcePairing_length G hfree hv p source
    rw [htwo] at hlen
    unfold oneHighGraphSourcePairing at hlen
    rw [matchingPairingListSorted_length, matchingPairingList_length] at hlen
    exact hlen
  have hrow : oneHighGraphSourcePairing G hfree hv p source = [key, key] := by
    rw [oneHighGraphSourcePairing]
    exact matchingPairingListSorted_eq_duplicate_of_two_sources
      M label key sx sy hcard hsx hsy hsxy hkeyx hkeyy
  rw [hrow]
  simp [oneHighGraphCanonicalSlotRow, htwo,
    oneHighPairingRowSlotVariants, key, hequal]

end

end Erdos85

#print axioms Erdos85.oneHighGraphCanonicalSlotRow_mem_variants_of_two_equal
