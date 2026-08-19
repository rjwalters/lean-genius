import Proofs.Erdos85SizeTwoMuNegOneEightEightAllTriangleParameterBounds

/-! # All-triangle-free parameter pressure in the `mu=-1` C8+C8 branch -/

open Finset Matrix

namespace Erdos85

noncomputable section

theorem alternating_C8_row_same_add_two_le_of_cycleOnes_local
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hminus : N 0 (-1) = 1) (hplus : N 0 1 = 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = f 0 ∧ N 0 j = 1).card + 2 ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1).card := by
  classical
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦
    f j = f 0 ∧ N 0 j = 1
  let R := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ N 0 j = 1
  have hneg (i : ZMod 8) (hi : f i = -f 0) : f i ≠ f 0 := by
    rcases hsign 0 with h0 | h0 <;> omega
  have hpT : (-1 : ZMod 8) ∉ T := by
    intro h
    have hs := (Finset.mem_filter.mp h).2.1
    have hf : f (-1) = -f 0 := by
      have h := hflip (-1)
      norm_num at h ⊢
      omega
    exact hneg _ hf hs
  have hqT : (1 : ZMod 8) ∉ T := by
    intro h
    have hs := (Finset.mem_filter.mp h).2.1
    exact hneg _ (by simpa using hflip 0) hs
  have hpq : (-1 : ZMod 8) ≠ 1 := by decide
  have hins : insert (-1) (insert 1 T) ⊆ R := by
    intro j hj
    simp only [Finset.mem_insert] at hj
    rcases hj with rfl | rfl | hj
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hminus⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplus⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2.2⟩
  have hcard : (insert (-1) (insert 1 T)).card = T.card + 2 := by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_insert_of_notMem hqT]
    · simp [hpT, hpq]
  have hle := Finset.card_le_card hins
  simpa [T, R, hcard] using hle

theorem alternating_C8_allTriangleFree_internal_parameter_upper_local
    (N : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ) (k r : ℕ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r)
    (hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ N 0 j = 1).card = k)
    (hminus : N 0 (-1) = 1) (hplus : N 0 1 = 1) :
    r + k ≤ 5 := by
  have hle := alternating_C8_row_same_add_two_le_of_cycleOnes_local
    N f hsign hflip hminus hplus
  rw [hNrow, hNsame] at hle
  omega

set_option maxHeartbeats 1200000 in
/-- On an all-triangle-free normalized C8 shore in the `mu=-1` branch,
the signed quotient capacity satisfies `r+k≤5`. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_allTriangleFree_parameter_bounds
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
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u : ZMod 8 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hallTfA : ∀ x : c.supp, x ∈ a.supp →
      (triangleFreeEdgeGraph G).degree x.1 = 2) :
    ∃ k r : ℕ, k ≤ 3 ∧ 2 ≤ r ∧ r ≤ 7 ∧ r + k ≤ 5 := by
  classical
  let Hc := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  obtain ⟨_ha8, _hb8, r, hr2, hr7, haa, _habq, _hbaq, _hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨k, hk, hA, _hB, _hcrossA, _hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_signedParameter
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
  have huiA : u 0 ∈ A := by
    change u 0 ∈ (↑A : Set c.supp)
    rw [← hurangeA]
    exact ⟨0, rfl⟩
  let N : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (u j)
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
  have hcycleOne (j : ZMod 8) (hj : j = -1 ∨ j = 1) : N 0 j = 1 := by
    let T := (Finset.univ : Finset c.supp).filter fun y ↦
      (triangleFreeEdgeGraph G).Adj (u 0).1 y.1
    have himage : Finset.image Subtype.val T =
        (triangleFreeEdgeGraph G).neighborFinset (u 0).1 := by
      ext y
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_neighborFinset]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro htf
        have hDxy : (secondOrderDefectGraph G).Adj (u 0).1 y := by
          have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u 0).1 y := by
            rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
            exact htf
          exact hpair.2
        have hyc : y ∈ c.supp := by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff c y]
          exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
            hDxy).symm.trans
              ((SimpleGraph.ConnectedComponent.mem_supp_iff c (u 0).1).mp
                (u 0).2)
        exact ⟨⟨y, hyc⟩, htf, rfl⟩
    have hTcard : T.card = 2 := by
      rw [← Finset.card_image_of_injective T Subtype.val_injective,
        himage, (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact hallTfA (u 0) (by simpa [A] using huiA)
    have hTsub : T ⊆ Hc.neighborFinset (u 0) := by
      intro y hy
      have htf := (Finset.mem_filter.mp hy).2
      have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u 0).1 y.1 := by
        rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
        exact htf
      exact (Hc.mem_neighborFinset (u 0) y).mpr hpair.1
    have hTeq : T = Hc.neighborFinset (u 0) := by
      apply Finset.eq_of_subset_of_card_le hTsub
      rw [hTcard, Hc.card_neighborFinset_eq_degree, hHdegree]
    have hHj : Hc.Adj (u 0) (u j) := by
      rw [← Hc.mem_neighborFinset, hu]
      rcases hj with rfl | rfl <;> simp
    have hujT : u j ∈ T := by
      rw [hTeq]
      exact (Hc.mem_neighborFinset (u 0) (u j)).mpr hHj
    have htf := (Finset.mem_filter.mp hujT).2
    have hpair : (G ⊓ secondOrderDefectGraph G).Adj (u 0).1 (u j).1 := by
      rw [← triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree]
      exact htf
    have hK : K.Adj (u 0) (u j) := hpair.2
    simp [N, SimpleGraph.adjMatrix_apply, hK]
  have hupper := alternating_C8_allTriangleFree_internal_parameter_upper_local
    N (fun i ↦ s (u i).1) k r (fun i ↦ hs_in _ (u i).2) hflip
      hNrow hNsame (hcycleOne (-1) (Or.inl rfl))
        (hcycleOne 1 (Or.inr rfl))
  exact ⟨k, r, hk, hr2, hr7, hupper⟩

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_allTriangleFree_parameter_bounds
