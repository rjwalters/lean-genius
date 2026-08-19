import Proofs.Erdos85SizeTwoEigenlineEightEightMixedExteriorModel

/-!
# Exterior-pair model for the both-all-triangle middle eight-plus-eight stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

/-- On an all-triangle C8 whose diagonal defect block has offsets `±3,4`,
the two opposite-sign offsets `±3` exhaust the global opposite-sign defect
budget.  Every defect edge leaving that shore therefore preserves sign. -/
theorem binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_cross_defect_preserves_sign
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
    (a : (G.induce c.supp).ConnectedComponent)
    (u : ZMod 8 → c.supp)
    (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hdiag : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5)
    (i : ZMod 8) (y : c.supp) (hy : y ∉ a.supp)
    (hxy : ((secondOrderDefectGraph G).induce c.supp).Adj (u i) y) :
    s y.1 = s (u i).1 := by
  classical
  let H := G.induce c.supp
  let D := secondOrderDefectGraph G
  let opposite : Finset V :=
    (D.neighborFinset (u i).1).filter fun z => s z = -s (u i).1
  have hoppCard : opposite.card = 2 := by
    simpa [opposite, D] using
      (sameSide_defect_degree G hfree (q := 8) (by omega) hreg hcard c s
        hs_in hDs (u i).2).2
  have huflip : ∀ k : ZMod 8, s (u (k + 1)).1 = -s (u k).1 := by
    intro k
    have hH : H.Adj (u k) (u (k + 1)) := by
      rw [← H.mem_neighborFinset, hu]
      simp
    have hmem : (u (k + 1)).1 ∈ componentNeighborFinset G D c (u k).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (u (k + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (u k).2).2 _ hmem
  have hsignEven := zmodEight_alternating_sign_eq_iff_evenOffset
    (fun k => s (u k).1) (fun k => hs_in _ (u k).2) huflip
  have hOppSign (k : ZMod 8)
      (hoff : k - i = 3 ∨ k - i = 5) :
      s (u k).1 = -s (u i).1 := by
    by_contra hne
    have heq : s (u k).1 = s (u i).1 := by
      rcases hs_in (u k).1 (u k).2 with hkNeg | hkPos <;>
        rcases hs_in (u i).1 (u i).2 with hiNeg | hiPos <;> simp_all
    have heven := (hsignEven i k).mp heq
    rcases hoff with h3 | h5
    · rw [h3] at heven
      revert heven
      decide
    · rw [h5] at heven
      revert heven
      decide
  let p : V := (u (i + 3)).1
  let q : V := (u (i + 5)).1
  let internalOpp : Finset V := {p, q}
  have hpq : p ≠ q := by
    intro h
    have huEq : u (i + 3) = u (i + 5) := Subtype.ext h
    have hz := huinj huEq
    have : (3 : ZMod 8) = 5 := by linear_combination hz
    exact (by decide : (3 : ZMod 8) ≠ 5) this
  have hinterCard : internalOpp.card = 2 := by simp [internalOpp, hpq]
  have hinterSub : internalOpp ⊆ opposite := by
    intro z hz
    simp only [internalOpp, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · apply (D.mem_neighborFinset _ _).mpr
        exact (hdiag i (i + 3)).mpr (Or.inl (by ring))
      · exact hOppSign (i + 3) (Or.inl (by ring))
    · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · apply (D.mem_neighborFinset _ _).mpr
        exact (hdiag i (i + 5)).mpr (Or.inr (Or.inr (by ring)))
      · exact hOppSign (i + 5) (Or.inr (by ring))
  have hinterEq : internalOpp = opposite :=
    Finset.eq_of_subset_of_card_le hinterSub (by rw [hinterCard, hoppCard])
  by_contra hsign
  have hySign : s y.1 = -s (u i).1 := by
    rcases hs_in y.1 y.2 with hyNeg | hyPos <;>
      rcases hs_in (u i).1 (u i).2 with hiNeg | hiPos <;> simp_all
  have hyOpp : y.1 ∈ opposite := Finset.mem_filter.mpr
    ⟨(D.mem_neighborFinset _ _).mpr hxy, hySign⟩
  rw [← hinterEq] at hyOpp
  simp only [internalOpp, Finset.mem_insert, Finset.mem_singleton] at hyOpp
  rcases hyOpp with hyp | hyq
  · apply hy
    rw [← hurange]
    exact ⟨i + 3, Subtype.ext hyp.symm⟩
  · apply hy
    rw [← hurange]
    exact ⟨i + 5, Subtype.ext hyq.symm⟩

/-- With cross quotient four, the preceding sign preservation fills all four
same-sign vertices of the opposite C8 and no others. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangle_parameter_four_cross_iff_sameSign
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
    (hdiag : ∀ i j : ZMod 8,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 3 ∨ j - i = 4 ∨ j - i = 5)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4) :
    ∀ x y : c.supp, x ∈ a.supp → y ∈ b.supp →
      (((secondOrderDefectGraph G).induce c.supp).Adj x y ↔
        s y.1 = s x.1) := by
  classical
  let H := G.induce c.supp
  let D := secondOrderDefectGraph G
  let K := D.induce c.supp
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcomm : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G D hglobal c).symm
  intro x y hxA hyB
  let B := componentNeighborFinset K H b x
  let S : Finset c.supp :=
    (Finset.univ.image v).filter fun z => s z.1 = s x.1
  have hBcard : B.card = 4 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hxA]
    simpa [K, H] using hab4
  have hBsign : ∀ z ∈ B, s z.1 = s x.1 := by
    intro z hz
    have hzK := (Finset.mem_filter.mp hz).1
    have hzb := (Finset.mem_filter.mp hz).2
    have hzbSupp : z ∈ b.supp :=
      (ConnectedComponent.mem_supp_iff b z).mpr hzb
    have hzNotA : z ∉ a.supp := by
      intro hza
      apply hab
      rw [← (ConnectedComponent.mem_supp_iff a z).mp hza,
        ← (ConnectedComponent.mem_supp_iff b z).mp hzbSupp]
    rw [← hurange] at hxA
    obtain ⟨i, rfl⟩ := hxA
    exact binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_cross_defect_preserves_sign
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a u huinj hurange
        hu hdiag i z hzNotA ((K.mem_neighborFinset _ _).mp hzK)
  have hvflip : ∀ j : ZMod 8, s (v (j + 1)).1 = -s (v j).1 := by
    intro j
    have hH : H.Adj (v j) (v (j + 1)) := by
      rw [← H.mem_neighborFinset, hv]
      simp
    have hmem : (v (j + 1)).1 ∈ componentNeighborFinset G D c (v j).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (v (j + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v j).2).2 _ hmem
  obtain ⟨hvSame, hvOpp⟩ := zmodEight_alternating_sign_filter_cards
    (fun j => s (v j).1) (fun j => hs_in _ (v j).2) hvflip
  have hBsubS : B ⊆ S := by
    intro z hz
    have hzb : z ∈ b.supp := (Finset.mem_filter.mp hz).2
    rw [← hvrange] at hzb
    obtain ⟨j, rfl⟩ := hzb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hBsign _ hz⟩
  have hScard : S.card = 4 := by
    have hfilterImage : S =
        ((Finset.univ : Finset (ZMod 8)).filter
          fun j => s (v j).1 = s x.1).image v := by
      ext z
      simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨⟨j, _, rfl⟩, hj⟩
        exact ⟨j, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j, rfl⟩, hj⟩
    rw [hfilterImage, Finset.card_image_of_injective _ hvinj]
    rcases hs_in x.1 x.2 with hxNeg | hxPos <;>
      rcases hs_in (v 0).1 (v 0).2 with hvNeg | hvPos <;> simp_all
  have hBS : B = S := Finset.eq_of_subset_of_card_le hBsubS (by omega)
  rw [← K.mem_neighborFinset]
  constructor
  · intro hxy
    have hyInB : y ∈ B := Finset.mem_filter.mpr ⟨hxy, hyB⟩
    have hyInS : y ∈ S := by rw [← hBS]; exact hyInB
    exact (Finset.mem_filter.mp hyInS).2
  · intro hsign
    rw [← hvrange] at hyB
    obtain ⟨j, rfl⟩ := hyB
    have hyInS : v j ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hsign⟩
    have hyInB : v j ∈ B := by rw [hBS]; exact hyInS
    exact (Finset.mem_filter.mp hyInB).1

/-- Exact exterior-pair graph of the both-all-triangle `8+8`, `r=4`
component: both shores have owner offsets `±1`, and cross-shore owners join
opposite signs. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_bothTriangle_parameterFour_exteriorPair_model
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
    (hallA : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
    (hallB : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3)
    (hbb3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b b = 3)
    (hab4 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 4) :
    (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (u i) (u j) ↔
        j - i = 1 ∨ j - i = 7) ∧
      (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
        j - i = 1 ∨ j - i = 7) ∧
      (∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (u i) (v j) ↔
        s (v j).1 ≠ s (u i).1) := by
  let H := G.induce c.supp
  have hDA :=
    binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_defectAdj_iff_offset_three_four_five
      G hfree hreg hcard c hc a u huinj hurange hu hallA haa3
  have hDB :=
    binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_defectAdj_iff_offset_three_four_five
      G hfree hreg hcard c hc b v hvinj hvrange hv hallB hbb3
  have hDcross :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangle_parameter_four_cross_iff_sameSign
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b hab u v huinj
        hvinj hurange hvrange hu hv hDA hab4
  have hua : ∀ i, H.connectedComponentMk (u i) = a := by
    intro i
    exact (ConnectedComponent.mem_supp_iff a (u i)).mp (by
      rw [← hurange]; exact ⟨i, rfl⟩)
  have hvb : ∀ j, H.connectedComponentMk (v j) = b := by
    intro j
    exact (ConnectedComponent.mem_supp_iff b (v j)).mp (by
      rw [← hvrange]; exact ⟨j, rfl⟩)
  have allShore
      (w : ZMod 8 → c.supp) (hwinj : Function.Injective w)
      (hw : ∀ z, H.neighborFinset (w z) = {w (z - 1), w (z + 1)})
      (hD : ∀ i j : ZMod 8,
        ((secondOrderDefectGraph G).induce c.supp).Adj (w i) (w j) ↔
          j - i = 3 ∨ j - i = 4 ∨ j - i = 5) :
      ∀ i j : ZMod 8, (exteriorPairGraph G c.supp).Adj (w i) (w j) ↔
        j - i = 1 ∨ j - i = 7 := by
    intro i j
    rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common G hfree c]
    have hcommon (hij : i ≠ j) :
        (∃ z, H.Adj (w i) z ∧ H.Adj (w j) z) ↔
          j - i = 2 ∨ j - i = 6 :=
      zmodEight_cycle_internalCommon_iff_offset_two_six H w hwinj hw i j hij
    constructor
    · rintro ⟨hij, hnotD, hnoCommon⟩
      have hij' : i ≠ j := fun h => hij (congrArg w h)
      have hnotD' : ¬ (j - i = 3 ∨ j - i = 4 ∨ j - i = 5) := by
        intro h
        exact hnotD ((hD i j).mpr h)
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
      refine ⟨hwinj.ne hij', ?_, ?_⟩
      · intro hDij
        have hd := (hD i j).mp (by simpa using hDij)
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
  refine ⟨allShore u huinj hu hDA, allShore v hvinj hv hDB, ?_⟩
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
    exact hnotD ((hDcross (u i) (v j) huiA hvjB).mpr hsign)
  · intro hsign
    refine ⟨hne, ?_, ?_⟩
    · intro hD
      exact hsign ((hDcross (u i) (v j) huiA hvjB).mp hD)
    · simpa [H] using hnoCommon

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_allTriangle_diagonalThree_cross_defect_preserves_sign
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangle_parameter_four_cross_iff_sameSign
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_bothTriangle_parameterFour_exteriorPair_model
