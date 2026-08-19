import Proofs.Erdos85SizeTwoEigenlineSixTenAllTfAntipodalShape
import Proofs.Erdos85SizeTwoEigenlineSixTenInternalCommonPairs
import Proofs.Erdos85ExteriorPairGraphAdjacency

/-!
# Exact long-shore model in the all-triangle-free six-plus-ten branch

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The offset-`±2` member of the all-TF long-shore antipodal dichotomy is
impossible: `v i` and `v (i+2)` have the ambient midpoint `v (i+1)` in
common.  Hence the antipodal support is exactly `±4`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_antipodal_offset_four
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
    ∀ i j, (antipodalGraph G).Adj (v i).1 (v j).1 ↔
      j - i = 4 ∨ j - i = 6 := by
  rcases
      binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_antipodal_offset_dichotomy
        G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
          v hvinj hvrange hv with htwo | hfour
  · exfalso
    have hanti : (antipodalGraph G).Adj (v 0).1 (v 2).1 := by
      apply (htwo 0 2).2
      left
      decide
    have h01 : G.Adj (v 0).1 (v 1).1 := by
      have hH : (G.induce c.supp).Adj (v 0) (v 1) := by
        rw [← (G.induce c.supp).mem_neighborFinset, hv]
        simp
      exact hH
    have h21 : G.Adj (v 2).1 (v 1).1 := by
      have hH : (G.induce c.supp).Adj (v 2) (v 1) := by
        rw [← (G.induce c.supp).mem_neighborFinset, hv]
        simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        apply congrArg v
        decide
      exact hH
    have hmem : (v 1).1 ∈
        G.neighborFinset (v 0).1 ∩ G.neighborFinset (v 2).1 := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_neighborFinset]
      exact ⟨h01, h21⟩
    have hzero := ((mem_antipodalNeighbors G (v 0).1 (v 2).1).mp hanti).2.2
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hmem
    exact Finset.notMem_empty _ hmem
  · exact hfour

/-- Consequently the long-shore exterior-pair graph in the all-TF branch
has exactly offsets `±3` and the antipodal offset `5`. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_exteriorPair_iff
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
    ∀ i j, (exteriorPairGraph G c.supp).Adj (v i) (v j) ↔
      j - i = 3 ∨ j - i = 5 ∨ j - i = 7 := by
  classical
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  have hvb : ∀ i, v i ∈ b.supp := by
    intro i
    rw [← hvrange]
    exact ⟨i, rfl⟩
  have hanti :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_antipodal_offset_four
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
        v hvinj hvrange hv
  have hD : ∀ i j, K.Adj (v i) (v j) ↔
      j - i = 1 ∨ j - i = 4 ∨ j - i = 6 ∨ j - i = 9 := by
    intro i j
    constructor
    · intro hK
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
        (v i).1 (v j).1 at hK
      rcases hK with haij | htf
      · rcases (hanti i j).mp haij with h4 | h6
        · exact Or.inr (Or.inl h4)
        · exact Or.inr (Or.inr (Or.inl h6))
      · have hG : G.Adj (v i).1 (v j).1 :=
          ((mem_triangleFreeNeighbors G (v i).1 (v j).1).mp
            ((triangleFreeEdgeGraph_adj G (v i).1 (v j).1).mp htf)).1
        have hmem : v j ∈ H.neighborFinset (v i) :=
          (H.mem_neighborFinset _ _).mpr hG
        rw [hv] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hm | hp
        · right; right; right
          have heq := hvinj hm
          calc
            j - i = (i - 1) - i := by rw [heq]
            _ = -1 := by ring
            _ = 9 := by decide
        · left
          have heq := hvinj hp
          calc
            j - i = (i + 1) - i := by rw [heq]
            _ = 1 := by ring
    · intro hoff
      rcases hoff with h1 | h4 | h6 | h9
      · have hH : H.Adj (v i) (v j) := by
          rw [← H.mem_neighborFinset, hv]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          right
          apply congrArg v
          calc
            j = i + (j - i) := by ring
            _ = i + 1 := by rw [h1]
        exact (binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_opposite_defectAdj_iff
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
            (v i) (v j) (hvb i) (hvb j)).mpr hH |>.1
      · change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
          (v i).1 (v j).1
        exact Or.inl ((hanti i j).mpr (Or.inl h4))
      · change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj
          (v i).1 (v j).1
        exact Or.inl ((hanti i j).mpr (Or.inr h6))
      · have hneg : j - i = -1 := h9.trans (by decide)
        have hH : H.Adj (v i) (v j) := by
          rw [← H.mem_neighborFinset, hv]
          simp only [Finset.mem_insert, Finset.mem_singleton]
          left
          apply congrArg v
          calc
            j = i + (j - i) := by ring
            _ = i - 1 := by rw [hneg]; ring
        exact (binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_opposite_defectAdj_iff
          G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb hbtf
            (v i) (v j) (hvb i) (hvb j)).mpr hH |>.1
  intro i j
  by_cases hij : i = j
  · subst j
    constructor
    · exact fun h => ((exteriorPairGraph G c.supp).loopless.irrefl _ h).elim
    · intro h
      have hn : ¬ (((0 : ZMod 10) = 3) ∨ (0 : ZMod 10) = 5 ∨
          (0 : ZMod 10) = 7) := by decide
      exact (hn (by simpa using h)).elim
  have hvij : v i ≠ v j := fun h => hij (hvinj h)
  have hcommon : (∃ z : c.supp,
      G.Adj (v i).1 z.1 ∧ G.Adj (v j).1 z.1) ↔
      j - i = 2 ∨ j - i = 8 := by
    have hex := zmodTen_cycle_internalCommon_iff_offset_two_eight
      H v hvinj hv i j hij
    constructor
    · rintro ⟨z, hiz, hjz⟩
      exact hex.mp ⟨z, hiz, hjz⟩
    · intro h
      obtain ⟨z, hiz, hjz⟩ := hex.mpr h
      exact ⟨z, hiz, hjz⟩
  rw [exteriorPairGraph_adj_iff_not_defect_and_no_internal_common
    G hfree c (v i) (v j)]
  change (v i ≠ v j ∧ ¬ K.Adj (v i) (v j) ∧
    ¬ (∃ z : c.supp, G.Adj (v i).1 z.1 ∧ G.Adj (v j).1 z.1)) ↔ _
  rw [hD, hcommon, and_iff_right hvij]
  letI : DecidableEq (ZMod 10) := ZMod.decidableEq 10
  fin_cases i <;> fin_cases j
  all_goals first | contradiction | decide

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_antipodal_offset_four
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTf_exteriorPair_iff
