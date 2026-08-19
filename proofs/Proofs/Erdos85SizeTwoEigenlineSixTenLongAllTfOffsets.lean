import Proofs.Erdos85ZModTenSameParityIntertwiner
import Proofs.Erdos85SizeTwoEigenlineSixTenCrossSign
import Proofs.Erdos85DefectCycleBlock

/-!
# Same-sign diagonal offsets in the q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 1000000 in
/-- Equality classes of a nonzero alternating sign function on `ZMod 10`
are exactly the even coordinate differences. -/
theorem zmodTen_alternating_sign_eq_iff_evenOffset_sub
    (g : ZMod 10 → ℤ)
    (hflip : ∀ j, g (j + 1) = -g j)
    (hsign : ∀ j, g j = -1 ∨ g j = 1) :
    ∀ i j, g j = g i ↔ ZModTenEvenOffset (j - i) := by
  have h1 := hflip 0
  have h2 := hflip 1
  have h3 := hflip 2
  have h4 := hflip 3
  have h5 := hflip 4
  have h6 := hflip 5
  have h7 := hflip 6
  have h8 := hflip 7
  have h9 := hflip 8
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9
  have h0ne : g 0 ≠ 0 := by
    rcases hsign 0 with hneg | hpos <;> omega
  have allCases : ∀ z : ZMod 10, z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 ∨ z = 4 ∨
      z = 5 ∨ z = 6 ∨ z = 7 ∨ z = 8 ∨ z = 9 := by decide
  intro i j
  rcases allCases i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases allCases j with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hsign 0 with h0 | h0 <;>
    norm_num [ZModTenEvenOffset, h1, h2, h3, h4, h5, h6, h7, h8, h9, h0] <;>
    decide

/-- In cyclic coordinates on the long component of a `6+10` size-two
configuration, its two same-sign diagonal defect neighbors occur globally
at offsets `{±2}` or globally at offsets `{±4}`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_sameSign_offset_dichotomy
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
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    (∀ i j, ZModTenEvenOffset (j - i) →
        (((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j) ↔
          j - i = 2 ∨ j - i = 8)) ∨
      (∀ i j, ZModTenEvenOffset (j - i) →
        (((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j) ↔
          j - i = 4 ∨ j - i = 6)) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let M : Matrix (ZMod 10) (ZMod 10) ℤ :=
    fun i j => K.adjMatrix ℤ (v i) (v j)
  have hvsign : ∀ j : ZMod 10, s (v (j + 1)).1 = -s (v j).1 := by
    intro j
    have hH : H.Adj (v j) (v (j + 1)) := by
      rw [← H.mem_neighborFinset, hv]
      simp
    have hmem : (v (j + 1)).1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c (v j).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hH, (v (j + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hA_in (v j).2).2 _ hmem
  have hsignParity : ∀ i j,
      s (v j).1 = s (v i).1 ↔ ZModTenEvenOffset (j - i) :=
    zmodTen_alternating_sign_eq_iff_evenOffset_sub
      (fun j => s (v j).1) hvsign (fun j => hs_in _ (v j).2)
  obtain ⟨hHdegree, _hKdegree, hcommHK⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree (by omega) hreg hcard c hc
  have hcommKH : K.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * K.adjMatrix ℤ := by
    simpa [K, H] using hcommHK.symm
  have hvpair : ∀ z : ZMod 10, v (z - 1) ≠ v (z + 1) := by
    intro z heq
    have hz : z - 1 = z + 1 := hvinj heq
    exact (by decide : (2 : ZMod 10) ≠ 0) (by
      calc
        (2 : ZMod 10) = (z + 1) - (z - 1) := by ring
        _ = 0 := by rw [← hz]; simp)
  have hinter : ∀ i j,
      M (i - 1) j + M (i + 1) j = M i (j + 1) + M i (j - 1) := by
    exact entry_cycleIntertwine_of_adjMatrix_comm K H v v
      (1 : ZMod 10) (1 : ZMod 10) hcommKH hv hv hvpair hvpair
  have hdiag : ∀ z, M z z = 0 := by
    intro z
    simp [M, SimpleGraph.adjMatrix_apply]
  have hsymm : ∀ i j, M i j = M j i := by
    intro i j
    simp [M, SimpleGraph.adjMatrix_apply, K.adj_comm]
  have hdegree : ∀ i,
      ((Finset.univ : Finset (ZMod 10)).filter fun j =>
        ZModTenEvenOffset (j - i) ∧ M i j = 1).card = 2 := by
    intro i
    let S := (Finset.univ : Finset (ZMod 10)).filter fun j =>
      ZModTenEvenOffset (j - i) ∧ M i j = 1
    let T := (componentNeighborFinset K H b (v i)).filter fun z =>
      s z.1 = s (v i).1
    have himage : S.image v = T := by
      ext z
      simp only [S, T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, componentNeighborFinset]
      constructor
      · rintro ⟨j, ⟨he, hM⟩, rfl⟩
        have hK : K.Adj (v i) (v j) := by
          simpa [M, SimpleGraph.adjMatrix_apply] using hM
        refine ⟨⟨(K.mem_neighborFinset _ _).mpr hK, ?_⟩, ?_⟩
        · exact (ConnectedComponent.mem_supp_iff b (v j)).mp
            (by rw [← hvrange]; exact ⟨j, rfl⟩)
        · exact (hsignParity i j).2 he
      · rintro ⟨⟨hzK, hzb⟩, hzsign⟩
        have hzb' : z ∈ b.supp :=
          (ConnectedComponent.mem_supp_iff b z).mpr hzb
        rw [← hvrange] at hzb'
        obtain ⟨j, rfl⟩ := hzb'
        refine ⟨j, ⟨(hsignParity i j).1 hzsign, ?_⟩, rfl⟩
        have hK : K.Adj (v i) (v j) :=
          (K.mem_neighborFinset _ _).mp hzK
        simp [M, SimpleGraph.adjMatrix_apply, hK]
    have hScard : S.card = T.card := by
      calc
        S.card = (S.image v).card :=
          (Finset.card_image_of_injective _ hvinj).symm
        _ = T.card := congrArg Finset.card himage
    have hTcard : T.card = 2 := by
      simpa [T, K, H] using
        (binarySquare_regular_sizeTwoPart_eight_sixTen_longDiagonal_signSplit
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
            (v i) (by rw [← hvrange]; exact ⟨i, rfl⟩)).1
    simpa [S, hTcard] using hScard
  rcases zmodTen_selfIntertwiner_sameParity_degreeTwo_offset_dichotomy
    M hdiag hsymm hinter hdegree with h | h
  · left
    intro i j he
    have hij := h i j he
    simpa [M, K, SimpleGraph.adjMatrix_apply] using hij
  · right
    intro i j he
    have hij := h i j he
    simpa [M, K, SimpleGraph.adjMatrix_apply] using hij

end

end Erdos85

#print axioms Erdos85.zmodTen_alternating_sign_eq_iff_evenOffset_sub
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_sameSign_offset_dichotomy
