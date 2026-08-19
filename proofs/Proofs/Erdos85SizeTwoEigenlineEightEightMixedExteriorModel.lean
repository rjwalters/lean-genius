import Proofs.Erdos85SizeTwoEigenlineEightEightLowExteriorModel
import Proofs.Erdos85SizeTwoEigenlineAllTriangleCycleDiagonal

/-!
# Exterior-pair model for the mixed middle eight-plus-eight stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

At quotient parameter four a mixed pair of C8 shores has one
all-triangle-free shore and one all-triangle shore.  This file identifies
the missing diagonal block of the latter: its three defect neighbours are
exactly the offsets `±3,4`.  Thus its exterior-pair edges have offsets
`±1`, while the triangle-free shore has offsets `±3` and the cross edges
join opposite signs.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- On an all-triangle internal C8 with diagonal defect quotient three,
the diagonal defect edges are exactly offsets `±3` and the half-turn. -/
theorem binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_defectAdj_iff_offset_three_four_five
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
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp)
    (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hall : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3) :
    ∀ i j : ZMod 8,
      (((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hua (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hcycleAdj (i j : ZMod 8) :
      H.Adj (u i) (u j) ↔ j - i = 1 ∨ j - i = 7 := by
    rw [← H.mem_neighborFinset, hu]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with h | h
      · right
        calc
          j - i = (i - 1) - i := congrArg (fun z => z - i) (huinj h)
          _ = -1 := by ring
          _ = 7 := by decide
      · left
        simpa using congrArg (fun z => z - i) (huinj h)
    · intro h
      rcases h with h | h
      · right
        exact congrArg u (by linear_combination h)
      · left
        apply congrArg u
        have hneg : j - i = -1 := h.trans (by decide)
        linear_combination hneg
  have hnotAdjacent (i j : ZMod 8) (hadj : H.Adj (u i) (u j)) :
      ¬ K.Adj (u i) (u j) := by
    intro hK
    change (secondOrderDefectGraph G).Adj (u i).1 (u j).1 at hK
    change (antipodalGraph G).Adj (u i).1 (u j).1 ∨
      (triangleFreeEdgeGraph G).Adj (u i).1 (u j).1 at hK
    rcases hK with hanti | htf
    · exact ((mem_antipodalNeighbors G (u i).1 (u j).1).mp hanti).2.1 hadj
    · have hmem : (u j).1 ∈
          (triangleFreeEdgeGraph G).neighborFinset (u i).1 :=
        ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf
      have hpos := Finset.card_pos.mpr ⟨(u j).1, hmem⟩
      rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        hall (u i) (hua i)] at hpos
      omega
  have hnotDistanceTwo (i j : ZMod 8)
      (hoff : j - i = 2 ∨ j - i = 6) : ¬ K.Adj (u i) (u j) := by
    have hij : i ≠ j := by
      intro h
      subst j
      have h02 : (0 : ZMod 8) ≠ 2 := by decide
      have h06 : (0 : ZMod 8) ≠ 6 := by decide
      simpa only [sub_self, h02, h06, or_self] using hoff
    obtain ⟨z, hiz, hjz⟩ :=
      (zmodEight_cycle_internalCommon_iff_offset_two_six
        H u huinj hu i j hij).mpr hoff
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree
      (fun h => huinj.ne hij (Subtype.ext h)) hiz hjz
  let T (i : ZMod 8) := (Finset.univ : Finset (ZMod 8)).filter fun j =>
    K.Adj (u i) (u j)
  have hTcard (i : ZMod 8) : (T i).card = 3 := by
    let B := componentNeighborFinset K H a (u i)
    have himage : (T i).image u = B := by
      ext z
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, B, componentNeighborFinset]
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(K.mem_neighborFinset _ _).mpr hj,
          (ConnectedComponent.mem_supp_iff a (u j)).mp (hua j)⟩
      · rintro ⟨hzK, hza⟩
        have hzA : z ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a z).mpr hza
        rw [← hurange] at hzA
        obtain ⟨j, rfl⟩ := hzA
        exact ⟨j, (K.mem_neighborFinset _ _).mp hzK, rfl⟩
    rw [← Finset.card_image_of_injective (T i) huinj, himage]
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a a (hua i)]
    exact haa3
  let S (i : ZMod 8) := (Finset.univ : Finset (ZMod 8)).filter fun j =>
    j - i = 3 ∨ j - i = 4 ∨ j - i = 5
  have hScard (i : ZMod 8) : (S i).card = 3 := by
    classical
    fin_cases i <;> decide
  have hsub (i : ZMod 8) : T i ⊆ S i := by
    intro j hj
    have hK : K.Adj (u i) (u j) := (Finset.mem_filter.mp hj).2
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    have hallOffsets : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨
        j - i = 6 ∨ j - i = 7 := by
      generalize j - i = d
      revert d
      decide
    rcases hallOffsets with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
    · have hij : i = j := by exact (sub_eq_zero.mp h0).symm
      exact False.elim (K.ne_of_adj hK (congrArg u hij))
    · exact False.elim (hnotAdjacent i j ((hcycleAdj i j).mpr (Or.inl h1)) hK)
    · exact False.elim (hnotDistanceTwo i j (Or.inl h2) hK)
    · exact Or.inl h3
    · exact Or.inr (Or.inl h4)
    · exact Or.inr (Or.inr h5)
    · exact False.elim (hnotDistanceTwo i j (Or.inr h6) hK)
    · exact False.elim (hnotAdjacent i j ((hcycleAdj i j).mpr (Or.inr h7)) hK)
  have heq (i : ZMod 8) : T i = S i := by
    exact Finset.eq_of_subset_of_card_le (hsub i) (by rw [hTcard, hScard])
  intro i j
  have hmemT : j ∈ T i ↔ K.Adj (u i) (u j) := by simp [T]
  have hmemS : j ∈ S i ↔ j - i = 3 ∨ j - i = 4 ∨ j - i = 5 := by
    simp [S]
  rw [← hmemT, heq, hmemS]

/-- Exact exterior-pair graph of the mixed `8+8`, `r=4` component.  The
triangle-free shore has owner offsets `±3`, the all-triangle shore has owner
offsets `±1`, and cross-shore owners join opposite signs. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_mixed_parameterFour_exteriorPair_model
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
    (hallB : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hbb3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4) :
    (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 5) ∧
      (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 7) ∧
      (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
        s (v j).1 ≠ s (u i).1) := by
  let H := G.induce c.supp
  have hDA :=
    binarySquare_regular_sizeTwoPart_eight_allTriangleFree_diagonalThree_defectAdj_iff_offset_one_or_four
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a u huinj hurange hu
        htfA haa3
  have hDB :=
    binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_defectAdj_iff_offset_three_four_five
      G hfree hreg hcard c hc b v hvinj hvrange hv hallB hbb3
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
  have tfShore : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 5 := by
    intro i j
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
    have hcommon (hij : i ≠ j) :
        (∃ z, H.Adj (u i) z ∧ H.Adj (u j) z) ↔
          j - i = 2 ∨ j - i = 6 :=
      zmodEight_cycle_internalCommon_iff_offset_two_six H u huinj hu i j hij
    constructor
    · rintro ⟨hij, hnotD, hnoCommon⟩
      have hij' : i ≠ j := fun h => hij (congrArg u h)
      have hnotD' : ¬ (j - i = 1 ∨ j - i = 7 ∨ j - i = 4) := by
        intro h
        apply hnotD
        exact (hDA i j).mpr h
      have hnotCommon : ¬ (j - i = 2 ∨ j - i = 6) := by
        intro h
        apply hnoCommon
        simpa [H] using (hcommon hij').mpr h
      have hall : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨
          j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨
          j - i = 6 ∨ j - i = 7 := by
        generalize j - i = d
        revert d
        decide
      have hnot0 : j - i ≠ 0 := by
        intro h0
        apply hij'
        exact (sub_eq_zero.mp h0).symm
      tauto
    · intro hoff
      have hij' : i ≠ j := by
        intro h
        subst j
        have h03 : (0 : ZMod 8) ≠ 3 := by decide
        have h05 : (0 : ZMod 8) ≠ 5 := by decide
        simpa only [sub_self, h03, h05, or_self] using hoff
      refine ⟨huinj.ne hij', ?_, ?_⟩
      · intro hD
        have hd := (hDA i j).mp (by simpa using hD)
        rcases hoff with h3 | h5
        · rw [h3] at hd
          revert hd
          decide
        · rw [h5] at hd
          revert hd
          decide
      · intro hex
        have hc := (hcommon hij').mp (by simpa [H] using hex)
        rcases hoff with h3 | h5
        · rw [h3] at hc
          revert hc
          decide
        · rw [h5] at hc
          revert hc
          decide
  have allShore : ∀ i j : ZMod 8,
      (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 7 := by
    intro i j
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
    have hcommon (hij : i ≠ j) :
        (∃ z, H.Adj (v i) z ∧ H.Adj (v j) z) ↔
          j - i = 2 ∨ j - i = 6 :=
      zmodEight_cycle_internalCommon_iff_offset_two_six H v hvinj hv i j hij
    constructor
    · rintro ⟨hij, hnotD, hnoCommon⟩
      have hij' : i ≠ j := fun h => hij (congrArg v h)
      have hnotD' : ¬ (j - i = 3 ∨ j - i = 4 ∨ j - i = 5) := by
        intro h
        apply hnotD
        exact (hDB i j).mpr h
      have hnotCommon : ¬ (j - i = 2 ∨ j - i = 6) := by
        intro h
        apply hnoCommon
        simpa [H] using (hcommon hij').mpr h
      have hall : j - i = 0 ∨ j - i = 1 ∨ j - i = 2 ∨
          j - i = 3 ∨ j - i = 4 ∨ j - i = 5 ∨
          j - i = 6 ∨ j - i = 7 := by
        generalize j - i = d
        revert d
        decide
      have hnot0 : j - i ≠ 0 := by
        intro h0
        apply hij'
        exact (sub_eq_zero.mp h0).symm
      tauto
    · intro hoff
      have hij' : i ≠ j := by
        intro h
        subst j
        have h01 : (0 : ZMod 8) ≠ 1 := by decide
        have h07 : (0 : ZMod 8) ≠ 7 := by decide
        simpa only [sub_self, h01, h07, or_self] using hoff
      refine ⟨hvinj.ne hij', ?_, ?_⟩
      · intro hD
        have hd := (hDB i j).mp (by simpa using hD)
        rcases hoff with h1 | h7
        · rw [h1] at hd
          revert hd
          decide
        · rw [h7] at hd
          revert hd
          decide
      · intro hex
        have hc := (hcommon hij').mp (by simpa [H] using hex)
        rcases hoff with h1 | h7
        · rw [h1] at hc
          revert hc
          decide
        · rw [h7] at hc
          revert hc
          decide
  refine ⟨tfShore, allShore, ?_⟩
  intro i j
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
  have huiA : u i ∈ a.supp := by rw [← hurange]; exact ⟨i, rfl⟩
  have hvjB : v j ∈ b.supp := by rw [← hvrange]; exact ⟨j, rfl⟩
  have hne : u i ≠ v j := by
    intro huv
    apply hab
    rw [← hua i, ← hvb j, huv]
  have hnoCommon := distinct_components_no_internalCommon
    H a b hab u v hua hvb i j
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

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_defectAdj_iff_offset_three_four_five
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_mixed_parameterFour_exteriorPair_model
