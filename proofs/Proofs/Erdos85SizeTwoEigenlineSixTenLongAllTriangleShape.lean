import Proofs.Erdos85SizeTwoEigenlineSixTenLongAllTriangleOddOffsets
import Proofs.Erdos85SizeTwoEigenlineSixTenCrossAntipodal
import Proofs.Erdos85SizeTwoEigenlineSixTenShortCycleRigidity

/-!
# Full antipodal shape of the all-triangle C10 shore

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The all-triangle C10 antipodal block has one of two global circulant
supports: `{±2, ±3}` or `{±3, ±4}`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_antipodal_shape
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
      {v (z - 1), v (z + 1)})
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) :
    (∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
      j - i = 2 ∨ j - i = 3 ∨ j - i = 7 ∨ j - i = 8) ∨
    (∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
      j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7) := by
  have hodd :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_odd_antipodal_offsets
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        v hvinj hvrange hv hball
  have heven := binarySquare_regular_sizeTwoPart_eight_sixTen_long_sameSign_offset_dichotomy
    G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
      v hvinj hvrange hv
  have hcolor : ∀ i j,
      (((secondOrderDefectGraph G).induce c.supp).Adj (v i) (v j) ↔
        (antipodalGraph G).Adj (v i).1 (v j).1) := by
    intro i j
    exact binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_defectAdj_iff_antipodal
      G c b hball (v i) (v j) (by rw [← hvrange]; exact ⟨i, rfl⟩)
  rcases heven with heven | heven
  · left
    intro i j
    by_cases hp : ZModTenEvenOffset (j - i)
    · have h := (hcolor i j).symm.trans (heven i j hp)
      constructor
      · intro ha
        rcases h.mp ha with h2 | h8
        · exact Or.inl h2
        · exact Or.inr (Or.inr (Or.inr h8))
      · intro ho
        apply h.mpr
        rcases ho with h2 | h3 | h7 | h8
        · exact Or.inl h2
        · exfalso
          rw [h3] at hp
          exact (by decide : ¬ ZModTenEvenOffset (3 : ZMod 10)) hp
        · exfalso
          rw [h7] at hp
          exact (by decide : ¬ ZModTenEvenOffset (7 : ZMod 10)) hp
        · exact Or.inr h8
    · have h := hodd i j hp
      constructor
      · intro ha
        rcases h.mp ha with h3 | h7
        · exact Or.inr (Or.inl h3)
        · exact Or.inr (Or.inr (Or.inl h7))
      · intro ho
        apply h.mpr
        rcases ho with h2 | h3 | h7 | h8
        · exfalso
          apply hp
          rw [h2]
          decide
        · exact Or.inl h3
        · exact Or.inr h7

        · exfalso
          apply hp
          rw [h8]
          decide
  · right
    intro i j
    by_cases hp : ZModTenEvenOffset (j - i)
    · have h := (hcolor i j).symm.trans (heven i j hp)
      constructor
      · intro ha
        rcases h.mp ha with h4 | h6
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr (Or.inl h6))
      · intro ho
        apply h.mpr
        rcases ho with h3 | h4 | h6 | h7
        · exfalso
          rw [h3] at hp
          exact (by decide : ¬ ZModTenEvenOffset (3 : ZMod 10)) hp
        · exact Or.inl h4
        · exact Or.inr h6
        · exfalso
          rw [h7] at hp
          exact (by decide : ¬ ZModTenEvenOffset (7 : ZMod 10)) hp
    · have h := hodd i j hp
      constructor
      · intro ha
        rcases h.mp ha with h3 | h7
        · exact Or.inl h3
        · exact Or.inr (Or.inr (Or.inr h7))
      · intro ho
        apply h.mpr
        rcases ho with h3 | h4 | h6 | h7
        · exact Or.inl h3
        · exfalso
          apply hp
          rw [h4]
          decide
        · exfalso
          apply hp
          rw [h6]
          decide
        · exact Or.inr h7

/-- Complete blockwise antipodal classification of the `6+10` branch whose
long shore is all-triangle. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_allTriangle_antipodal_shape
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
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
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
          j - i = 2 ∨ j - i = 3 ∨ j - i = 7 ∨ j - i = 8) ∨
        (∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
          j - i = 3 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 7)) := by
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
    have hmem := (antipodalGraph_adj G (u i).1 (u j).1).mp hanti
    exact ((mem_antipodalNeighbors G (u i).1 (u j).1).mp hmem).2.1 hH
  have hcross :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_crossAntipodal_iff_sign_eq_of_coordinates
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        u v huinj hvinj hurange hvrange hu hv
  have hlong :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_antipodal_shape
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        v hvinj hvrange hv hball
  exact ⟨hshort, hcross, hlong⟩

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_antipodal_shape
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_allTriangle_antipodal_shape
