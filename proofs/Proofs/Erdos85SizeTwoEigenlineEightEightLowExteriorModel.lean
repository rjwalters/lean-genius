import Proofs.Erdos85SizeTwoEigenlineEightEightMiddleSignSplit
import Proofs.Erdos85ExteriorPairGraphAdjacency
import Proofs.Erdos85SizeTwoEigenlineSixTenInternalCommonPairs

/-!
# Exterior-pair model for the low eight-plus-eight stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

When both C8 shores are all-triangle-free at quotient parameter four, the
internal defect blocks are now explicit.  The exterior-pair criterion then
identifies the owner graph: offset `±3` within a shore and opposite
eigenline sign across the shores.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- On a cyclically labeled C8, two distinct vertices have an internal common
neighbor exactly when their coordinate difference is `±2`. -/
theorem zmodEight_cycle_internalCommon_iff_offset_two_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)}) :
    ∀ i j, i ≠ j → ((∃ z, H.Adj (u i) z ∧ H.Adj (u j) z) ↔
      j - i = 2 ∨ j - i = 6) := by
  have hadj : ∀ i z, H.Adj (u i) z ↔
      z = u (i - 1) ∨ z = u (i + 1) := by
    intro i z
    rw [← H.mem_neighborFinset, hu]
    simp
  intro i j hij
  constructor
  · rintro ⟨z, hiz, hjz⟩
    rcases (hadj i z).1 hiz with hz | hz <;>
      rcases (hadj j z).1 hjz with hz' | hz'
    · have h := huinj (hz.symm.trans hz')
      exfalso
      apply hij
      linear_combination h
    · have h := huinj (hz.symm.trans hz')
      right
      have hneg : j - i = -2 := by
        calc
          j - i = (j + 1) - 1 - i := by ring
          _ = (i - 1) - 1 - i := by rw [h]
          _ = -2 := by ring
      calc
        j - i = -2 := hneg
        _ = 6 := by decide
    · have h := huinj (hz.symm.trans hz')
      left
      calc
        j - i = (j - 1) + 1 - i := by ring
        _ = (i + 1) + 1 - i := by rw [← h]
        _ = 2 := by ring
    · have h := huinj (hz.symm.trans hz')
      exfalso
      apply hij
      linear_combination h
  · intro h
    rcases h with h2 | h6
    · refine ⟨u (i + 1), (hadj i _).2 (Or.inr rfl), ?_⟩
      apply (hadj j _).2
      left
      apply congrArg u
      calc
        i + 1 = i + (j - i) - 1 := by rw [h2]; ring
        _ = j - 1 := by ring
    · refine ⟨u (i - 1), (hadj i _).2 (Or.inl rfl), ?_⟩
      apply (hadj j _).2
      right
      apply congrArg u
      have hneg : j - i = -2 := h6.trans (by decide)
      calc
        i - 1 = i + (j - i) + 1 := by rw [hneg]; ring
        _ = j + 1 := by ring

/-- Exact exterior-pair graph of the all-triangle-free `8+8`, `r=4`
component: within-cycle edges have offset `±3`, and cross-cycle edges join
opposite signs. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameterFour_exteriorPair_model
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (htfA : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (htfB : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hbb3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4) :
    (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 5) ∧
      (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
        j - i = 3 ∨ j - i = 5) ∧
      (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
        s (v j).1 ≠ s (u i).1) := by
  let H := G.induce c.supp
  have hDA :=
    binarySquare_regular_sizeTwoPart_eight_allTriangleFree_diagonalThree_defectAdj_iff_offset_one_or_four
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a u huinj hurange hu
        htfA haa3
  have hDB :=
    binarySquare_regular_sizeTwoPart_eight_allTriangleFree_diagonalThree_defectAdj_iff_offset_one_or_four
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs b v hvinj hvrange hv
        htfB hbb3
  have hDcross :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameter_four_cross_iff_sameSign
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b hab v hvinj
        hvrange hv htfA hab4
  have hua : ∀ i, H.connectedComponentMk (u i) = a := by
    intro i
    exact (ConnectedComponent.mem_supp_iff a (u i)).mp (by
      rw [← hurange]; exact ⟨i, rfl⟩)
  have hvb : ∀ j, H.connectedComponentMk (v j) = b := by
    intro j
    exact (ConnectedComponent.mem_supp_iff b (v j)).mp (by
      rw [← hvrange]; exact ⟨j, rfl⟩)
  have sameShore
      (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
      (hw : ∀ z, H.neighborFinset (w z) = {w (z - 1), w (z + 1)})
      (hD : ∀ i j : ZMod 8,
        ((secondOrderDefectGraph G).induce c.supp).Adj (w i) (w j) ↔
          j - i = 1 ∨ j - i = 7 ∨ j - i = 4) :
      ∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (w i) (w j) ↔
        j - i = 3 ∨ j - i = 5 := by
    intro i j
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
    constructor
    · rintro ⟨hij, hnotD, hnoCommon⟩
      have hij' : i ≠ j := fun h => hij (congrArg w h)
      have hnotD' : ¬ (j - i = 1 ∨ j - i = 7 ∨ j - i = 4) := by
        intro h
        apply hnotD
        exact hD i j |>.mpr h
      have hnotCommon : ¬ (j - i = 2 ∨ j - i = 6) := by
        intro h
        apply hnoCommon
        have hex := (zmodEight_cycle_internalCommon_iff_offset_two_six
          H w hwinj hw i j hij').mpr h
        simpa [H] using hex
      have hall : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨ j - i = 3 ∨
          j - i = 4 ∨ j - i = 5 ∨ j - i = 6 ∨ j - i = 7 := by
        generalize j - i = d
        revert d
        decide
      have hnot0 : j - i ≠ 0 := by
        intro h0
        apply hij'
        exact (sub_eq_zero.mp h0).symm
      tauto
    · intro hoff
      have hneCoord : i ≠ j := by
        intro h
        subst j
        rw [sub_self] at hoff
        revert hoff
        decide
      refine ⟨hwinj.ne hneCoord, ?_, ?_⟩
      · intro hDij
        have := (hD i j).mp (by simpa using hDij)
        rcases hoff with h3 | h5
        · rw [h3] at this
          revert this
          decide
        · rw [h5] at this
          revert this
          decide
      · intro hex
        have hcommon := (zmodEight_cycle_internalCommon_iff_offset_two_six
          H w hwinj hw i j hneCoord).mp (by simpa [H] using hex)
        rcases hoff with h3 | h5
        · rw [h3] at hcommon
          revert hcommon
          decide
        · rw [h5] at hcommon
          revert hcommon
          decide
  refine ⟨sameShore u huinj hu hDA, sameShore v hvinj hv hDB, ?_⟩
  intro i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have huiA : u i ∈ a.supp := by rw [← hurange]; exact ⟨i, rfl⟩
  have hvjB : v j ∈ b.supp := by rw [← hvrange]; exact ⟨j, rfl⟩
  have hne : u i ≠ v j := by
    intro huv
    apply hab
    rw [← hua i, ← hvb j, huv]
  have hnoCommon := distinct_components_no_internalCommon H a b hab u v hua hvb i j
  constructor
  · rintro ⟨_, hnotD, _⟩
    intro hsign
    apply hnotD
    have := (hDcross (u i) (v j) huiA hvjB).mpr hsign
    simpa using this
  · intro hsign
    refine ⟨hne, ?_, ?_⟩
    · intro hD
      apply hsign
      apply (hDcross (u i) (v j) huiA hvjB).mp
      simpa using hD
    · simpa [H] using hnoCommon

end

end Erdos85

#print axioms Erdos85.zmodEight_cycle_internalCommon_iff_offset_two_six
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameterFour_exteriorPair_model
