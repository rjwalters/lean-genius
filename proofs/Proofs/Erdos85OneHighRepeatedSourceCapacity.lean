import Proofs.Erdos85OneHighGlobalMissLabelCounting
import Proofs.Erdos85OneHighRawPresentation
import Proofs.Erdos85MatchingPairingRefinement

/-! # Capacity forced by repeated matching-edge owners -/

namespace Erdos85

open SimpleGraph

noncomputable section

set_option maxHeartbeats 800000

/-- In every canonical mate pair, at least one endpoint is a profile
two-edge branch.  Only the low endpoint can belong to the one-edge prefix. -/
theorem oneHighFamilyInternalEdges_eq_two_or_mate_eq_two
    (profile : Nat) (i : Fin 8) :
    oneHighFamilyInternalEdges profile i = 2 ∨
      oneHighFamilyInternalEdges profile (oneHighStandardMate i) = 2 := by
  fin_cases i <;>
    simp [oneHighFamilyInternalEdges, oneHighStandardMate_val_eq_xor]

/-- Two distinct globally oriented internal matching edges owned by the same
root branch force that branch to be one of the profile's two-edge branches. -/
theorem oneHighFamilyInternalEdges_eq_two_of_distinct_sources_sameOwner
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    {x y : OneHighAllMatchedVertices G v}
    (hx : x ∈ nonconstantMatchingEdgeSources
      (oneHighGlobalInternalMate G hfree v)
      (fun z => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj z)))
    (hy : y ∈ nonconstantMatchingEdgeSources
      (oneHighGlobalInternalMate G hfree v)
      (fun z => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj z)))
    (hxy : x ≠ y) (howner : x.1 = y.1) :
    oneHighFamilyInternalEdges p.profile (p.branchLabel x.1) = 2 := by
  rcases x with ⟨s, x⟩
  rcases y with ⟨t, y⟩
  change s = t at howner
  subst t
  let M := oneHighInternalMate G hfree v s
  have hMInv : Function.Involutive M := degreeOneMate_involutive _ _
  have hMNe : ∀ z, M z ≠ z := degreeOneMate_ne _ _
  have hGMInv : Function.Involutive (oneHighGlobalInternalMate G hfree v) :=
    oneHighGlobalInternalMate_involutive G hfree v
  have hxSource : (⟨s, x⟩ : OneHighAllMatchedVertices G v) ∈
      matchingEdgeSources (oneHighGlobalInternalMate G hfree v) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hx).2.1⟩
  have hySource : (⟨s, y⟩ : OneHighAllMatchedVertices G v) ∈
      matchingEdgeSources (oneHighGlobalInternalMate G hfree v) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp hy).2.1⟩
  have hdisjoint := matchingEdgeSources_disjoint_mateImage
    (oneHighGlobalInternalMate G hfree v) hGMInv
  have hxy' : x ≠ y := by
    intro h
    apply hxy
    subst y
    rfl
  have hxM : x ≠ M x := (hMNe x).symm
  have hyM : y ≠ M y := (hMNe y).symm
  have hMxMy : M x ≠ M y := fun h => hxy' (hMInv.injective h)
  have hXGMY : (⟨s, x⟩ : OneHighAllMatchedVertices G v) ≠
      oneHighGlobalInternalMate G hfree v ⟨s, y⟩ := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint hxSource
      (Finset.mem_image.mpr ⟨⟨s, y⟩, hySource, h.symm⟩))
  have hGMXY : oneHighGlobalInternalMate G hfree v
      (⟨s, x⟩ : OneHighAllMatchedVertices G v) ≠ ⟨s, y⟩ := by
    intro h
    exact (Finset.disjoint_left.mp hdisjoint hySource
      (Finset.mem_image.mpr ⟨⟨s, x⟩, hxSource, h⟩))
  have hxMy : x ≠ M y := by
    intro h
    apply hXGMY
    change (⟨s, x⟩ : OneHighAllMatchedVertices G v) = ⟨s, M y⟩
    congr
  have hMxY : M x ≠ y := by
    intro h
    apply hGMXY
    change (⟨s, M x⟩ : OneHighAllMatchedVertices G v) = ⟨s, y⟩
    congr
  let f : Fin 4 → OneHighMatchedBranchVertices G v s := fun i =>
    if i = 0 then x else if i = 1 then M x else if i = 2 then y else M y
  have hf : Function.Injective f := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [f, hxy', hxy'.symm, hxM, (hMNe x), hyM, (hMNe y),
        hMxMy, hMxMy.symm, hxMy, hxMy.symm, hMxY, hMxY.symm]
  have hfour : 4 ≤ Fintype.card (OneHighMatchedBranchVertices G v s) := by
    simpa using Fintype.card_le_of_injective f hf
  have hcard : Fintype.card (OneHighMatchedBranchVertices G v s) =
      2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) := by
    calc
      Fintype.card (OneHighMatchedBranchVertices G v s) =
          highBranchMatchedCount G v s :=
        card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount G v s
      _ = 2 * oneHighFamilyInternalEdges p.profile (p.branchLabel s) :=
        by simpa using p.matched_count (p.branchLabel s)
  have hedge : oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 1 ∨
      oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 2 := by
    unfold oneHighFamilyInternalEdges
    split <;> simp
  change oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 2
  rcases hedge with hedge | hedge <;> omega

end

end Erdos85
