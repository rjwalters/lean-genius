import Proofs.Erdos85SizeTwoEigenlineEightEightHighSignSplit

/-!
# Cross antipodal saturation in the high eight-plus-eight sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

Across distinct internal components, no ambient G-edge exists.  Therefore
cross defect adjacency is exactly antipodal adjacency.  At the forced
parameter six, the four same-sign cross neighbours exhaust the four-vertex
same-sign class of the opposite alternating C8.
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

/-- On the high `8+8` cross block, K-adjacency is antipodal adjacency, and
every equal-sign coordinate pair is adjacent. -/
theorem binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_crossAntipodal_saturation
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
    (∀ i j,
      ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (v j) ↔
        (antipodalGraph G).Adj (u i).1 (v j).1) ∧
      (∀ i j, s (v j).1 = s (u i).1 →
        (antipodalGraph G).Adj (u i).1 (v j).1) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hua (i : ZMod 8) : u i ∈ a.supp := by
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hvb (j : ZMod 8) : v j ∈ b.supp := by
    rw [← hvrange]
    exact ⟨j, rfl⟩
  have hnotG (i j : ZMod 8) : ¬G.Adj (u i).1 (v j).1 := by
    intro hG
    have hH : H.Adj (u i) (v j) := hG
    have heq : a = b := by
      rw [← (ConnectedComponent.mem_supp_iff a (u i)).mp (hua i),
        ← (ConnectedComponent.mem_supp_iff b (v j)).mp (hvb j)]
      exact ConnectedComponent.connectedComponentMk_eq_of_adj hH
    exact hab heq
  have hcrossIff : ∀ i j, K.Adj (u i) (v j) ↔
      (antipodalGraph G).Adj (u i).1 (v j).1 := by
    intro i j
    constructor
    · intro hK
      exact antipodal_adj_of_defect_adj_of_not_adj G hK (hnotG i j)
    · intro hanti
      exact Or.inl hanti
  have hsplit :=
    binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_firstCycle_signSplit
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hab
        u v huinj hvinj hurange hvrange hu hv hab6
  have hvflip : ∀ j : ZMod 8, s (v (j + 1)).1 = -s (v j).1 := by
    intro j
    have hH : H.Adj (v j) (v (j + 1)) := by
      rw [← H.mem_neighborFinset, hv]
      simp
    have hmem : (v (j + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (v j).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (v (j + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v j).2).2 _ hmem
  obtain ⟨hvSame, hvOpp⟩ := zmodEight_alternating_sign_filter_cards
    (fun j => s (v j).1) (fun j => hs_in _ (v j).2) hvflip
  have hsameK (i j : ZMod 8) (hsign : s (v j).1 = s (u i).1) :
      K.Adj (u i) (v j) := by
    let B := (componentNeighborFinset K H b (u i)).filter
      fun z => s z.1 = s (u i).1
    let S : Finset c.supp := (Finset.univ.image v).filter
      fun z => s z.1 = s (u i).1
    have hBcard : B.card = 4 := by
      simpa [B, K, H] using (hsplit i).2.2.1
    have hBsubS : B ⊆ S := by
      intro z hz
      have hzB := (Finset.mem_filter.mp hz).1
      have hzSign := (Finset.mem_filter.mp hz).2
      have hzb : z ∈ b.supp :=
        (ConnectedComponent.mem_supp_iff b z).mpr (Finset.mem_filter.mp hzB).2
      rw [← hvrange] at hzb
      obtain ⟨k, rfl⟩ := hzb
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩, hzSign⟩
    have hScard : S.card = 4 := by
      have hfilterImage : S =
          ((Finset.univ : Finset (ZMod 8)).filter
            fun k => s (v k).1 = s (u i).1).image v := by
        ext z
        simp only [S, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨⟨k, _, rfl⟩, hk⟩
          exact ⟨k, hk, rfl⟩
        · rintro ⟨k, hk, rfl⟩
          exact ⟨⟨k, rfl⟩, hk⟩
      rw [hfilterImage, Finset.card_image_of_injective _ hvinj]
      rcases hs_in (u i).1 (u i).2 with huNeg | huPos <;>
        rcases hs_in (v 0).1 (v 0).2 with hvNeg | hvPos <;>
        simp_all
    have hBeqS : B = S := Finset.eq_of_subset_of_card_le hBsubS (by omega)
    have hvjS : v j ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩, hsign⟩
    rw [← hBeqS] at hvjS
    exact (K.mem_neighborFinset _ _).mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hvjS).1).1
  refine ⟨?_, ?_⟩
  · intro i j
    exact hcrossIff i j
  · intro i j hsign
    exact (hcrossIff i j).mp (hsameK i j hsign)

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_eightEight_parameterSix_crossAntipodal_saturation
