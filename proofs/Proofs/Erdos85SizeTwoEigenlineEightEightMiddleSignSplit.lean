import Proofs.Erdos85SizeTwoEigenlineEightEightHighParameterSix
import Proofs.Erdos85SizeTwoEigenlineAllTriangleFreeCrossSign

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
    have hzNotA : z ∉ a.supp := by
      intro hza
      apply hab
      rw [← (ConnectedComponent.mem_supp_iff a z).mp hza,
        ← (ConnectedComponent.mem_supp_iff b z).mp hzb]
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

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_allTriangleFree_middle_parameter_eq_four
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameter_five_both_allTriangle
