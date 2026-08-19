import Proofs.Erdos85SizeTwoMuNegThreeEightEightSharpParameterBounds
import Proofs.Erdos85TriangleFreeSecondOrderIntersection

/-! # All-triangle parameter pressure in the `mu=-3` C8+C8 branch -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- A subset of a four-element set that avoids two distinct specified
elements has cardinality at most two. -/
theorem card_le_two_of_subset_card_four_avoid_two
    {α : Type*} [DecidableEq α] (S T : Finset α) (p q : α)
    (hS : S.card = 4) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    (hsub : T ⊆ S) (hpT : p ∉ T) (hqT : q ∉ T) :
    T.card ≤ 2 := by
  have hins : insert p (insert q T) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact hp
    · exact hq
    · exact hsub hx
  have hcard : (insert p (insert q T)).card = T.card + 2 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem hqT]
    · simp [hpT, hpq]
  have := Finset.card_le_card hins
  rw [hcard, hS] at this
  omega

/-- If the two cycle-neighbor entries vanish, an alternating C8 row has at
most two opposite-sign entries. -/
theorem alternating_C8_row_card_le_same_add_two_of_cycleZeros
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hminus : N 0 (-1) ≠ 1) (hplus : N 0 1 ≠ 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1).card ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card + 2 := by
  classical
  let S := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ f j ≠ f 0
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    f j ≠ f 0 ∧ N 0 j = 1
  have hS : S.card = 4 :=
    (zmodEight_alternating_sign_class_cards_four
      f hsign hflip (f 0) (hsign 0)).2
  have hneg (i : ZMod 8) (hi : f i = -f 0) : f i ≠ f 0 := by
    rcases hsign 0 with h0 | h0 <;> omega
  have hp : (-1 : ZMod 8) ∈ S := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hneg _ ?_⟩
    have h := hflip (-1)
    norm_num at h ⊢
    omega
  have hq : (1 : ZMod 8) ∈ S := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hneg _ (by simpa using hflip 0)⟩
  have hpq : (-1 : ZMod 8) ≠ 1 := by decide
  have hsub : T ⊆ S := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.1⟩
  have hpT : (-1 : ZMod 8) ∉ T := by
    intro h
    exact hminus (Finset.mem_filter.mp h).2.2
  have hqT : (1 : ZMod 8) ∉ T := by
    intro h
    exact hplus (Finset.mem_filter.mp h).2.2
  have hTle : T.card ≤ 2 :=
    card_le_two_of_subset_card_four_avoid_two S T (-1) 1
      hS hp hq hpq hsub hpT hqT
  let R := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ f j = f 0) (s := R)
  have hsame : (R.filter fun j ↦ f j = f 0).card =
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card := by
    congr 1
    ext j
    simp [R, and_comm]
  have hopp : (R.filter fun j ↦ ¬ f j = f 0).card = T.card := by
    congr 1
    ext j
    simp [R, T, and_comm]
  calc
    R.card = (R.filter fun j ↦ f j = f 0).card +
        (R.filter fun j ↦ ¬ f j = f 0).card := hpart.symm
    _ ≤ (R.filter fun j ↦ f j = f 0).card + 2 :=
      Nat.add_le_add_left (by simpa [hopp] using hTle) _
    _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card + 2 := by rw [hsame]

/-- An internal quotient row of size `7-r`, with same-sign degree `k`,
forces `5 ≤ r+k` once its two cycle-neighbor entries vanish. -/
theorem alternating_C8_allTriangle_internal_parameter_lower
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ) (k r : ℕ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r)
    (hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ N 0 j = 1).card = k)
    (hminus : N 0 (-1) ≠ 1) (hplus : N 0 1 ≠ 1) :
    5 ≤ r + k := by
  have hle := alternating_C8_row_card_le_same_add_two_of_cycleZeros
    N f hsign hflip hminus hplus
  rw [hNrow, hNsame] at hle
  omega

set_option maxHeartbeats 1200000 in
/-- On an all-triangle normalized C8 shore in the `mu=-3` branch, the
signed quotient capacity is exactly in the window `5 ≤ r+k ≤ 6`. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_allTriangle_parameter_bounds
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
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hallA : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 0) :
    ∃ k r : ℕ, k ≤ 2 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      5 ≤ r + k ∧ r + k ≤ 6 := by
  classical
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  obtain ⟨_ha8, _hb8, r, hr2, hr7, haa, habq, _hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨k, hk, hA, _hB, hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegThree_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hHdegree : ∀ z : c.supp, Hc.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2)
        (by simpa [Nat.mul_comm] using hc) z
  have hcommReal : K.adjMatrix ℝ * Hc.adjMatrix ℝ =
      Hc.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hvrangeB : Set.range v = ↑B := by
    rw [hvrange]
    ext x
    simp [B]
  have huiA : u 0 ∈ A := by
    change u 0 ∈ (↑A : Set c.supp)
    rw [← hurangeA]
    exact ⟨0, rfl⟩
  let N : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  have hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (u j)) by
      ext j; simp [N, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K A u huinj hurangeA (u 0)]
    have hqcard : (componentNeighborFinset K Hc a (u 0)).card = 7 - r := by
      rw [← componentQuotientMatrix_apply_eq K Hc 2 hHdegree hcommReal
        a a (by simpa [A] using huiA)]
      exact haa
    have heq : A.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K Hc a (u 0) := by
      ext y
      simp [A, Hc, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hMrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      M 0 j = 1).card = r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K B v hvinj hvrangeB (u 0)]
    have hqcard : (componentNeighborFinset K Hc b (u 0)).card = r := by
      rw [← componentQuotientMatrix_apply_eq K Hc 2 hHdegree hcommReal
        a b (by simpa [A] using huiA)]
      exact habq
    have heq : B.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K Hc b (u 0) := by
      ext y
      simp [B, Hc, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j).1 = s (u 0).1 ∧ N 0 j = 1).card = k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u 0).1 ∧ N 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (u j).1 = s (u 0).1 ∧ K.Adj (u 0) (u j)) by
      ext j; simp [N, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) 0]
    exact hA (u 0) huiA
  have hMsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (v j).1 = s (u 0).1 ∧ M 0 j = 1).card = 2 - k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (u 0).1 ∧ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (v j).1 = s (u 0).1 ∧ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support_from K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) (u 0)]
    exact hcrossA (u 0) huiA
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have hflip : ∀ i, s (u (i + 1)).1 = -s (u i).1 := by
    intro i
    have hadj : Hc.Adj (u i) (u (i + 1)) := by
      rw [← Hc.mem_neighborFinset, hu]
      simp
    have hmem : (u (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (u i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (u (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (u i).2).2 _ hmem
  have hflipV : ∀ i, s (v (i + 1)).1 = -s (v i).1 := by
    intro i
    have hadj : Hc.Adj (v i) (v (i + 1)) := by
      rw [← Hc.mem_neighborFinset, hv]
      simp
    have hmem : (v (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (v i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (v (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (v i).2).2 _ hmem
  have hcycleZero (j : ZMod 8) (hj : j = -1 ∨ j = 1) : N 0 j ≠ 1 := by
    intro hNj
    have hK : K.Adj (u 0) (u j) := by
      simpa [N, SimpleGraph.adjMatrix_apply] using hNj
    have hHc : Hc.Adj (u 0) (u j) := by
      rw [← Hc.mem_neighborFinset, hu]
      rcases hj with rfl | rfl <;> simp
    have htf : (triangleFreeEdgeGraph G).Adj (u 0).1 (u j).1 := by
      rw [triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
      exact ⟨hHc, hK⟩
    have hpos : 0 < (triangleFreeEdgeGraph G).degree (u 0).1 := by
      rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨(u j).1,
        ((triangleFreeEdgeGraph G).mem_neighborFinset _ _).mpr htf⟩
    have hzero := hallA (u 0) (by simpa [A] using huiA)
    omega
  have hlower := alternating_C8_allTriangle_internal_parameter_lower
    N (fun i ↦ s (u i).1) k r (fun i ↦ hs_in _ (u i).2) hflip
      hNrow hNsame (hcycleZero (-1) (Or.inl rfl))
        (hcycleZero 1 (Or.inr rfl))
  have hbounds := alternating_C8_internal_cross_parameter_bounds N M
    (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r hk
    (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
    hflip hflipV hNrow hNsame hMrow hMsame
  refine ⟨k, r, hk, hr2, hr7, hlower, ?_⟩
  exact hbounds.2.1

end

end Erdos85

#print axioms Erdos85.card_le_two_of_subset_card_four_avoid_two
#print axioms Erdos85.alternating_C8_row_card_le_same_add_two_of_cycleZeros
#print axioms Erdos85.alternating_C8_allTriangle_internal_parameter_lower
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_allTriangle_parameter_bounds
