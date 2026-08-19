import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTfOffsets
import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTfRigidity
import Proofs.Erdos85SizeTwoEigenlineSixTenCrossAntipodal
import Proofs.Erdos85SizeTwoEigenlineSixTenShortCycleRigidity

/-!
# Antipodal shape of the all-triangle-free q=8 six-plus-ten stratum

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

The long same-sign defect support is globally `{±2}` or `{±4}`.  In the
all-triangle-free branch the opposite-sign defect edges are exactly the
ambient C10 edges, hence are not antipodal.  Thus the support dichotomy is
also the exact antipodal adjacency classification on the long shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the all-TF `6+10` branch, long-shore antipodal adjacency is globally
the offset pair `{±2}` or globally the offset pair `{±4}`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_antipodal_offset_dichotomy
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
    (hbtf : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    (∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
        j - i = 2 ∨ j - i = 8) ∨
      (∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
        j - i = 4 ∨ j - i = 6) := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hvb : ∀ i, v i ∈ b.supp := by
    intro i
    rw [← hvrange]
    exact ⟨i, rfl⟩
  have hvflip : ∀ j : ZMod 10, s (v (j + 1)).1 = -s (v j).1 := by
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
      (fun j => s (v j).1) hvflip (fun j => hs_in _ (v j).2)
  have hanti_of_K_same : ∀ i j, K.Adj (v i) (v j) →
      s (v j).1 = s (v i).1 →
      (antipodalGraph G).Adj (v i).1 (v j).1 := by
    intro i j hK hsign
    have hnotG : ¬ G.Adj (v i).1 (v j).1 := by
      intro hG
      have hmem : (v j).1 ∈
          componentNeighborFinset G (secondOrderDefectGraph G) c (v i).1 := by
        rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset _ _).mpr hG, (v j).2⟩
      have hflip := (internal_alternation G hfree (by omega) hreg hcard c hc s
        hs_in hs_out hA_in (v i).2).2 _ hmem
      rcases hs_in (v i).1 (v i).2 with hineg | hipos <;> omega
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
      (v i).1 (v j).1 at hK
    rcases hK with hanti | htf
    · exact hanti
    · exact False.elim (hnotG
        ((mem_triangleFreeNeighbors G (v i).1 (v j).1).mp
          ((triangleFreeEdgeGraph_adj G (v i).1 (v j).1).mp htf)).1)
  have hK_of_anti : ∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 →
      K.Adj (v i) (v j) := by
    intro i j hanti
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
      (v i).1 (v j).1
    exact Or.inl hanti
  have hsame_of_anti : ∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 →
      s (v j).1 = s (v i).1 := by
    intro i j hanti
    have hnotG : ¬ G.Adj (v i).1 (v j).1 :=
      ((mem_antipodalNeighbors G (v i).1 (v j).1).mp hanti).2.1
    have hK := hK_of_anti i j hanti
    rcases hs_in (v i).1 (v i).2 with hineg | hipos <;>
      rcases hs_in (v j).1 (v j).2 with hjneg | hjpos
    · exact hjneg.trans hineg.symm
    · exfalso
      have hopp : s (v j).1 = -s (v i).1 := by omega
      have hH :=
        (binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_opposite_defectAdj_iff
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
            (v i) (v j) (hvb i) (hvb j)).1 ⟨hK, hopp⟩
      exact hnotG hH
    · exfalso
      have hopp : s (v j).1 = -s (v i).1 := by omega
      have hH :=
        (binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_opposite_defectAdj_iff
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
            (v i) (v j) (hvb i) (hvb j)).1 ⟨hK, hopp⟩
      exact hnotG hH
    · exact hjpos.trans hipos.symm
  obtain hoff | hoff :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_long_sameSign_offset_dichotomy
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        v hvinj hvrange hv
  · left
    intro i j
    constructor
    · intro hanti
      exact (hoff i j ((hsignParity i j).1 (hsame_of_anti i j hanti))).1
        (hK_of_anti i j hanti)
    · intro hd
      have heven : ZModTenEvenOffset (j - i) := by
        rcases hd with hd | hd <;> rw [hd] <;> decide
      exact hanti_of_K_same i j ((hoff i j heven).2 hd)
        ((hsignParity i j).2 heven)
  · right
    intro i j
    constructor
    · intro hanti
      exact (hoff i j ((hsignParity i j).1 (hsame_of_anti i j hanti))).1
        (hK_of_anti i j hanti)
    · intro hd
      have heven : ZModTenEvenOffset (j - i) := by
        rcases hd with hd | hd <;> rw [hd] <;> decide
      exact hanti_of_K_same i j ((hoff i j heven).2 hd)
        ((hsignParity i j).2 heven)

/-- Complete blockwise antipodal classification of the all-TF `6+10`
configuration: no short-shore antipodal edges, the sign-equality cross block,
and one of the two long-shore offset patterns. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_allTf_antipodal_shape
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
    (hbtf : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 2)
    (u : ZMod 6 → c.supp) (v : ZMod 10 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    (∀ i j, ¬ (antipodalGraph G).Adj (u i).1 (u j).1) ∧
      (∀ i j, (antipodalGraph G).Adj (u i).1 (v j).1 ↔
        s (v j).1 = s (u i).1) ∧
      ((∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
          j - i = 2 ∨ j - i = 8) ∨
        (∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
          j - i = 4 ∨ j - i = 6)) := by
  classical
  have hua : ∀ i, u i ∈ a.supp := by
    intro i
    rw [← hurange]
    exact ⟨i, rfl⟩
  have hshort : ∀ i j, ¬ (antipodalGraph G).Adj (u i).1 (u j).1 := by
    intro i j hanti
    have hK : ((secondOrderDefectGraph G).induce c.supp).Adj (u i) (u j) := by
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
        (u i).1 (u j).1
      exact Or.inl hanti
    have hH :=
      (binarySquare_regular_sizeTwoPart_eight_sixTen_shortCycle_defectAdj_iff
        G hfree hreg hcard c hc s hs_in hs_out hA_in a b ha hb
          (u i) (u j) (hua i) (hua j)).1 hK
    exact ((mem_antipodalNeighbors G (u i).1 (u j).1).mp hanti).2.1 hH
  have hcross :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_crossAntipodal_iff_sign_eq_of_coordinates
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv
  have hlong :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_antipodal_offset_dichotomy
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
        v hvinj hvrange hv
  exact ⟨hshort, hcross, hlong⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_antipodal_offset_dichotomy
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_allTf_antipodal_shape
