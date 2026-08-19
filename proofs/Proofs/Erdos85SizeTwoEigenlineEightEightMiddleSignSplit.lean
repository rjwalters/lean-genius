import Proofs.Erdos85SizeTwoEigenlineEightEightHighParameterSix
import Proofs.Erdos85SizeTwoEigenlineAllTriangleFreeCrossSign
import Proofs.Erdos85SizeTwoEigenlineEightEightLowAntipodalTrace
import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalMatching

/-!
# Middle-parameter sign rigidity for the eight-plus-eight stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

If either C8 shore is all-triangle-free, its two ambient neighbors exhaust
the opposite-sign defect budget.  Hence its cross-defect row preserves sign.
An opposite C8 shore contains only four vertices of either sign, so a middle
quotient parameter `r ≥ 4` must in fact equal four (and `r = 5` is excluded).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- In a coordinated `8+8` component, an all-triangle-free first shore and
a middle cross quotient force the quotient parameter to be exactly four. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_middle_parameter_eq_four
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (r : ℕ) (hr4 : 4 ≤ r)
    (habr : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = r) :
    r = 4 := by
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
  let x : c.supp := u 0
  let B := componentNeighborFinset K H b x
  have hxA : x ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  have hBcard : B.card = r := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hxA]
    simpa [K, H] using habr
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
    exact binarySquare_regular_sizeTwoPart_allTriangleFree_cross_defect_preserves_sign
      G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in hDs a htf
        x z hxA hzNotA ((K.mem_neighborFinset x z).mp hzK)
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
  let S : Finset c.supp := (Finset.univ.image v).filter fun z => s z.1 = s x.1
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
  have hrle : r ≤ 4 := by
    rw [← hBcard, ← hScard]
    exact Finset.card_le_card hBsubS
  omega

/-- In a coordinated `8+8` component, quotient parameter five forces both
internal eight-cycles into the all-triangle sector. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameter_five_both_allTriangle
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
    (ha : a.supp.ncard = 8) (hb : b.supp.ncard = 8) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hab5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 5)
    (hba5 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a = 5) :
    (∀ x : c.supp, x ∈ a.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) ∧
      (∀ x : c.supp, x ∈ b.supp →
        (triangleFreeEdgeGraph G).degree x.1 = 0) := by
  have shoreA : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0 := by
    rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc a with hall | htf
    · exact hall
    · have h54 :=
        binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_middle_parameter_eq_four
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
            u v huinj hvinj hurange hvrange hu hv htf 5 (by omega) hab5
      omega
  have shoreB : ∀ x : c.supp, x ∈ b.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0 := by
    rcases binarySquare_regular_sizeTwoPart_internalCycle_sector_dichotomy
      G hfree (by omega) (by decide) hreg hcard c hc b with hall | htf
    · exact hall
    · have h54 :=
        binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_middle_parameter_eq_four
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs b a hb ha hab.symm
            v u hvinj huinj hvrange hurange hv hu htf 5 (by omega) hba5
      omega
  exact ⟨shoreA, shoreB⟩

/-- At quotient parameter four, an all-triangle-free first shore has a cross
defect edge to exactly the four vertices of the second shore with the same
eigenline sign. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameter_four_cross_iff_sameSign
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
    (v : ZMod 8 → c.supp)
    (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
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
  let S : Finset c.supp := (Finset.univ.image v).filter fun z => s z.1 = s x.1
  have hBcard : B.card = 4 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hxA]
    simpa [K, H] using hab4
  have hBsubS : B ⊆ S := by
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
    have hzsign :=
      binarySquare_regular_sizeTwoPart_allTriangleFree_cross_defect_preserves_sign
        G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in hDs a htf
          x z hxA hzNotA ((K.mem_neighborFinset x z).mp hzK)
    rw [← hvrange] at hzbSupp
    obtain ⟨j, rfl⟩ := hzbSupp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hzsign⟩
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

/-- On an all-triangle-free internal C8 with diagonal defect quotient three,
the diagonal defect edges are exactly the two cycle edges and the half-turn. -/
theorem binarySquare_regular_sizeTwoPart_eight_allTriangleFree_diagonalThree_defectAdj_iff_offset_one_or_four
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
    (htf : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (haa3 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a = 3) :
    ∀ i j : ZMod 8,
      (((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) ↔
        j - i = 1 ∨ j - i = 7 ∨ j - i = 4) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let M : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j => K.adjMatrix ℤ (u i) (u j)
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  obtain ⟨_hHdegree', _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcomm : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  have hupair : ∀ z, u (z - 1) ≠ u (z + 1) := fun z =>
    huinj.ne (zmod_sub_one_ne_add_one_of_three_le (by omega) z)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    simpa only [M] using entry_cycleIntertwine_of_adjMatrix_comm
      K H u u (1 : ZMod 8) (1 : ZMod 8) hcomm hu hu hupair hupair
  have hdiag : ∀ z, M z z = 0 := by
    intro z
    simp [M, SimpleGraph.adjMatrix_apply]
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    by_cases hij : K.Adj (u i) (u j)
    · have hji : K.Adj (u j) (u i) := (K.adj_comm _ _).mp hij
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
    · have hji : ¬K.Adj (u j) (u i) := by
        intro h
        exact hij ((K.adj_comm _ _).mp h)
      simp [M, SimpleGraph.adjMatrix_apply, hij, hji]
  have huflip : ∀ i : ZMod 8, s (u (i + 1)).1 = -s (u i).1 := by
    intro i
    have hH : H.Adj (u i) (u (i + 1)) := by
      rw [← H.mem_neighborFinset, hu]
      simp
    have hmem : (u (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (u i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (u (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (u i).2).2 _ hmem
  have hsignEven := zmodEight_alternating_sign_eq_iff_evenOffset
    (fun i => s (u i).1) (fun i => hs_in _ (u i).2) huflip
  have hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 8)).filter fun j =>
        ZModEightEvenOffset (j - i) ∧ M i j = 1).card = 1 := by
    intro i
    let B := componentNeighborFinset K H a (u i)
    let N := H.neighborFinset (u i)
    let A := B.filter fun z => s z.1 = s (u i).1
    have huiA : u i ∈ a.supp := by
      rw [← hurange]
      exact ⟨i, rfl⟩
    have hBcard : B.card = 3 := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal a a huiA]
      simpa [K, H] using haa3
    have hNcard : N.card = 2 := by
      simpa [N] using H.card_neighborFinset_eq_degree (u i) |>.trans (hHdegree (u i))
    have hNsubB : N ⊆ B := by
      intro z hz
      have hiz : H.Adj (u i) z := (H.mem_neighborFinset _ _).mp hz
      have hzA : z ∈ a.supp := by
        rw [ConnectedComponent.mem_supp_iff]
        exact (ConnectedComponent.connectedComponentMk_eq_of_adj hiz).symm.trans
          ((ConnectedComponent.mem_supp_iff a (u i)).mp huiA)
      have htfEdge : (triangleFreeEdgeGraph G).Adj (u i).1 z.1 :=
        sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree (u i) z hiz
          (htf (u i) huiA)
      change z ∈ componentNeighborFinset K H a (u i)
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(K.mem_neighborFinset _ _).mpr (Or.inr htfEdge),
        (ConnectedComponent.mem_supp_iff a z).mp hzA⟩
    have hAeq : A = B \ N := by
      ext z
      constructor
      · intro hz
        have hzB := (Finset.mem_filter.mp hz).1
        have hzsign := (Finset.mem_filter.mp hz).2
        refine Finset.mem_sdiff.mpr ⟨hzB, ?_⟩
        intro hzN
        have hiz : H.Adj (u i) z := (H.mem_neighborFinset _ _).mp hzN
        have hmem : z.1 ∈ componentNeighborFinset G
            (secondOrderDefectGraph G) c (u i).1 := by
          rw [componentNeighborFinset, Finset.mem_filter]
          exact ⟨(G.mem_neighborFinset _ _).mpr hiz, z.2⟩
        have hopp := (internal_alternation G hfree (by omega) hreg hcard c hc s
          hs_in hs_out hA_in (u i).2).2 _ hmem
        rcases hs_in (u i).1 (u i).2 with hiNeg | hiPos <;> omega
      · intro hz
        have hzB := (Finset.mem_sdiff.mp hz).1
        have hzNotN := (Finset.mem_sdiff.mp hz).2
        have hzK := (Finset.mem_filter.mp hzB).1
        have hzsign :=
          binarySquare_regular_sizeTwoPart_allTriangleFree_nonambient_defect_preserves_sign
            G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in hDs a htf
              (u i) z huiA ((K.mem_neighborFinset _ _).mp hzK)
              (by simpa [N, H] using hzNotN)
        exact Finset.mem_filter.mpr ⟨hzB, hzsign⟩
    have hAcard : A.card = 1 := by
      rw [hAeq, Finset.card_sdiff, Finset.inter_eq_left.mpr hNsubB,
        hBcard, hNcard]
    let T := (Finset.univ : Finset (ZMod 8)).filter fun j =>
      ZModEightEvenOffset (j - i) ∧ M i j = 1
    have himage : T.image u = A := by
      ext z
      constructor
      · simp only [Finset.mem_image, T, Finset.mem_filter, Finset.mem_univ,
          true_and]
        rintro ⟨j, ⟨heven, hm⟩, rfl⟩
        have hadj : K.Adj (u i) (u j) := by
          simpa [M, SimpleGraph.adjMatrix_apply] using hm
        have hujA : u j ∈ a.supp := by
          rw [← hurange]
          exact ⟨j, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr
            ⟨(K.mem_neighborFinset _ _).mpr hadj,
              (ConnectedComponent.mem_supp_iff a (u j)).mp hujA⟩,
            (hsignEven i j).mpr heven⟩
      · intro hz
        have hzB := (Finset.mem_filter.mp hz).1
        have hzSign := (Finset.mem_filter.mp hz).2
        have hza : z ∈ a.supp :=
          (ConnectedComponent.mem_supp_iff a z).mpr (Finset.mem_filter.mp hzB).2
        rw [← hurange] at hza
        obtain ⟨j, rfl⟩ := hza
        have hadj := (K.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hzB).1
        refine Finset.mem_image.mpr ⟨j, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,
          (hsignEven i j).mp hzSign,
          by simpa [M, SimpleGraph.adjMatrix_apply, hadj]⟩
    rw [← Finset.card_image_of_injective T huinj, himage]
    exact hAcard
  have hoff := zmodEight_selfIntertwiner_sameParity_degreeOne_offset_four
    M hdiag hsymm hinter hdegree
  intro i j
  have hplus : ∀ p q : ZMod 8, q - p = 1 → q = p + 1 := by decide
  have hminus : ∀ p q : ZMod 8, q - p = 7 → q = p - 1 := by decide
  have hHadj : H.Adj (u i) (u j) ↔ j - i = 1 ∨ j - i = 7 := by
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
        exact congrArg u (hplus i j h)
      · left
        exact congrArg u (hminus i j h)
  constructor
  · intro hij
    by_cases hamb : H.Adj (u i) (u j)
    · exact (hHadj.mp hamb).elim Or.inl (fun h => Or.inr (Or.inl h))
    · right; right
      have hsame :=
        binarySquare_regular_sizeTwoPart_allTriangleFree_nonambient_defect_preserves_sign
          G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in hDs a htf
            (u i) (u j) (by rw [← hurange]; exact ⟨i, rfl⟩) hij hamb
      have heven := (hsignEven i j).mp hsame
      exact (hoff i j heven).mp (by
        change K.Adj (u i) (u j) at hij
        simpa [M, SimpleGraph.adjMatrix_apply] using hij)
  · intro h
    rcases h with h1 | h7 | h4
    · have hamb := hHadj.mpr (Or.inl h1)
      have htfEdge := sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree
        (u i) (u j) hamb (htf (u i) (by rw [← hurange]; exact ⟨i, rfl⟩))
      exact Or.inr htfEdge
    · have hamb := hHadj.mpr (Or.inr h7)
      have htfEdge := sizeTwo_triangleFreeEdge_of_degree_two G c hHdegree
        (u i) (u j) hamb (htf (u i) (by rw [← hurange]; exact ⟨i, rfl⟩))
      exact Or.inr htfEdge
    · have heven : ZModEightEvenOffset (j - i) := Or.inr (Or.inr (Or.inl h4))
      have hm := (hoff i j heven).mpr h4
      change K.Adj (u i) (u j)
      simpa [M, SimpleGraph.adjMatrix_apply] using hm

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_middle_parameter_eq_four
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameter_five_both_allTriangle
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_parameter_four_cross_iff_sameSign
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_allTriangleFree_diagonalThree_defectAdj_iff_offset_one_or_four
