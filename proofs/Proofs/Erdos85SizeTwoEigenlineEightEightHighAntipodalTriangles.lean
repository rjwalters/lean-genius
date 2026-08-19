import Proofs.Erdos85SizeTwoEigenlineEightEightHighAntipodalMatching

/-!
# Antipodal triangles in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Each forced diagonal half-turn edge has two six-element cross defect
neighbourhoods inside the opposite eight-cycle.  Their intersection has at
least four vertices.  Component separation makes every cross defect edge
antipodal, and the half-turn edge is antipodal as well.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem antipodal_adj_of_defect_adj_of_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V} (hD : (secondOrderDefectGraph G).Adj x y)
    (hnot : ¬ G.Adj x y) :
    (antipodalGraph G).Adj x y := by
  change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y at hD
  rcases hD with hanti | htf
  · exact hanti
  · exact False.elim (hnot
      ((mem_triangleFreeNeighbors G x y).mp
        ((triangleFreeEdgeGraph_adj G x y).mp htf)).1)

/-- Every diagonal half-turn edge on the first high-sector C8 supports at
least four antipodal triangles with third vertex on the opposite C8. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
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
    (hab6 : componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b = 6) :
    ∀ i : ZMod 8,
      (antipodalGraph G).Adj (u i).1 (u (i + 4)).1 ∧
      4 ≤ ((componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b (u i)) ∩
        componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b
            (u (i + 4))).card ∧
      (∀ z ∈ (componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b (u i)) ∩
        componentNeighborFinset
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b
            (u (i + 4)),
        (antipodalGraph G).Adj (u i).1 z.1 ∧
          (antipodalGraph G).Adj (u (i + 4)).1 z.1) := by
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
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  intro i
  let x := u i
  let y := u (i + 4)
  let A := componentNeighborFinset K H b x
  let B := componentNeighborFinset K H b y
  have hxA : x ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hyA : y ∈ a.supp := by
    rw [← hurange]
    exact ⟨i + 4, rfl⟩
  have hAcard : A.card = 6 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hxA]
    simpa [K, H] using hab6
  have hBcard : B.card = 6 := by
    rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcomm a b hyA]
    simpa [K, H] using hab6
  let S : Finset c.supp := b.supp.toFinite.toFinset
  have hUnionSub : A ∪ B ⊆ S := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · have hzb := (Finset.mem_filter.mp hz).2
      simpa [S] using (ConnectedComponent.mem_supp_iff b z).mpr hzb
    · have hzb := (Finset.mem_filter.mp hz).2
      simpa [S] using (ConnectedComponent.mem_supp_iff b z).mpr hzb
  have hScard : S.card = 8 := by
    simpa [S] using (Set.ncard_eq_toFinset_card' b.supp).symm.trans hb
  have hUnionCard : (A ∪ B).card ≤ 8 := by
    rw [← hScard]
    exact Finset.card_le_card hUnionSub
  have hInterCard : 4 ≤ (A ∩ B).card := by
    have hie := Finset.card_union_add_card_inter A B
    omega
  have hxyK : K.Adj x y := by
    apply (binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_defectAdj_iff_halfTurn
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv hab6 i (i + 4)).2
    ring
  have hnotGxy : ¬ G.Adj x.1 y.1 := by
    intro hG
    have hH : H.Adj x y := hG
    have hmem := (H.mem_neighborFinset x y).mpr hH
    rw [hu] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hminus | hplus
    · have hi := huinj hminus
      have : (4 : ZMod 8) = -1 := by linear_combination hi
      exact (by decide : (4 : ZMod 8) ≠ -1) this
    · have hi := huinj hplus
      have : (4 : ZMod 8) = 1 := by linear_combination hi
      exact (by decide : (4 : ZMod 8) ≠ 1) this
  have hxyAnti : (antipodalGraph G).Adj x.1 y.1 :=
    antipodal_adj_of_defect_adj_of_not_adj G hxyK hnotGxy
  have crossAnti (w : c.supp) (hwB : w ∈ b.supp)
      {p : c.supp} (hpA : p ∈ a.supp) (hpw : K.Adj p w) :
      (antipodalGraph G).Adj p.1 w.1 := by
    have hnotG : ¬ G.Adj p.1 w.1 := by
      intro hG
      have hH : H.Adj p w := hG
      have heq : a = b := by
        rw [← (ConnectedComponent.mem_supp_iff a p).mp hpA,
          ← (ConnectedComponent.mem_supp_iff b w).mp hwB]
        exact ConnectedComponent.connectedComponentMk_eq_of_adj hH
      exact hab heq
    exact antipodal_adj_of_defect_adj_of_not_adj G hpw hnotG
  refine ⟨by simpa [x, y] using hxyAnti, by simpa [A, B] using hInterCard, ?_⟩
  intro z hz
  have hzA := (Finset.mem_inter.mp hz).1
  have hzB := (Finset.mem_inter.mp hz).2
  have hzb : z ∈ b.supp :=
    (ConnectedComponent.mem_supp_iff b z).mpr (Finset.mem_filter.mp hzA).2
  have hxz : K.Adj x z :=
    (K.mem_neighborFinset x z).mp (Finset.mem_filter.mp hzA).1
  have hyz : K.Adj y z :=
    (K.mem_neighborFinset y z).mp (Finset.mem_filter.mp hzB).1
  exact ⟨by simpa [x] using crossAnti z hzb hxA hxz,
    by simpa [y] using crossAnti z hzb hyA hyz⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_four_antipodalTriangles
