import Proofs.Erdos85SizeTwoMuNegOneSectorSwitchRouting

/-! # Aligned quotient, sign, and sector ledger for μ=-1 -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- One shared `(k,r)` witness carrying every graph ledger consumed by the
μ=-1 cell terminals. -/
theorem orderSixtyFour_sizeTwo_muNegOne_eightEight_alignedLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2) (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-1 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (u v : ZMod 8 → c.supp)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)}) :
    let H := G.induce c.supp
    let K := (secondOrderDefectGraph G).induce c.supp
    let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
    let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
    let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (u i) (u j)
    let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ :=
      fun i j ↦ K.adjMatrix ℤ (v i) (v j)
    ∃ k r : ℕ,
      k ≤ 1 ∧ 2 ≤ r ∧ r ≤ 7 ∧ 3 ≤ r + k ∧ r + k ≤ 7 ∧
      a.supp.ncard = 8 ∧ b.supp.ncard = 8 ∧
      componentQuotientMatrix K H a a = 7 - r ∧
      componentQuotientMatrix K H a b = r ∧
      componentQuotientMatrix K H b a = r ∧
      componentQuotientMatrix K H b b = 7 - r ∧
      (∀ x ∈ A, (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = k) ∧
      (∀ x ∈ B, (B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = k) ∧
      (∀ x ∈ A, (B.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = 3 - k) ∧
      (∀ x ∈ B, (A.filter fun y ↦ K.Adj x y ∧ s y.1 = s x.1).card = 3 - k) ∧
      (MuNegOneC8CycleEntriesZero N₁ ∨ MuNegOneC8CycleEntriesOne N₁) ∧
      (MuNegOneC8CycleEntriesZero N₂ ∨ MuNegOneC8CycleEntriesOne N₂) ∧
      ((MuNegOneC8CycleEntriesZero N₁ ∧ MuNegOneC8CycleEntriesZero N₂ ∧
          5 ≤ r + k) ∨
        ((((MuNegOneC8CycleEntriesZero N₁ ∧ MuNegOneC8CycleEntriesOne N₂) ∨
            (MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesZero N₂)) ∧
              r + k = 5) ∨
          (MuNegOneC8CycleEntriesOne N₁ ∧ MuNegOneC8CycleEntriesOne N₂ ∧
            r + k ≤ 5))) := by
  classical
  dsimp only
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let B := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ b.supp
  let N₁ : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦ K.adjMatrix ℤ (u i) (u j)
  let N₂ : Matrix (ZMod 8) (ZMod 8) ℤ := fun i j ↦ K.adjMatrix ℤ (v i) (v j)
  obtain ⟨ha8, hb8, r, hr2, hr7, haa, habq, hbaq, hbb⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_distinctCycles_eightEight
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  obtain ⟨k, hk, hA, hB, hcrossA, hcrossB⟩ :=
    orderSixtyFour_sizeTwo_muNegOne_eightEight_signedParameter
      G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
  have hsector₁ : MuNegOneC8CycleEntriesZero N₁ ∨ MuNegOneC8CycleEntriesOne N₁ := by
    simpa [N₁, K] using
      (binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector_muNegOne
        G hfree hreg hcard c hc a u hurange hu)
  have hsector₂ : MuNegOneC8CycleEntriesZero N₂ ∨ MuNegOneC8CycleEntriesOne N₂ := by
    simpa [N₂, K] using
      (binarySquare_regular_sizeTwoPart_eight_normalizedCycle_entries_sector_muNegOne
        G hfree hreg hcard c hc b v hvrange hv)
  have hurangeA : Set.range u = ↑A := by
    rw [hurange]
    ext x
    simp [A]
  have hu0A : u 0 ∈ A := by
    change u 0 ∈ (↑A : Set c.supp)
    rw [← hurangeA]
    exact ⟨0, rfl⟩
  have hvrangeB : Set.range v = ↑B := by
    rw [hvrange]
    ext x
    simp [B]
  have hv0B : v 0 ∈ B := by
    change v 0 ∈ (↑B : Set c.supp)
    rw [← hvrangeB]
    exact ⟨0, rfl⟩
  have hHdegree : ∀ z : c.supp, H.degree z = 2 := by
    intro z
    exact binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (by omega) hreg hcard c (m := 2) hc z
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm G
      (secondOrderDefectGraph G) hglobal c).symm
  have hrow₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₁ 0 j = 1).card = 7 - r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N₁ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (u j)) by
      ext j; simp [N₁, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K A u huinj hurangeA (u 0)]
    have hqcard : (componentNeighborFinset K H a (u 0)).card = 7 - r := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal
        a a (by simpa [A] using hu0A)]
      exact haa
    have heq : A.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K H a (u 0) := by
      ext y
      simp [A, H, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hrow₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N₂ 0 j = 1).card = 7 - r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ N₂ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (v 0) (v j)) by
      ext j; simp [N₂, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K B v hvinj hvrangeB (v 0)]
    have hqcard : (componentNeighborFinset K H b (v 0)).card = 7 - r := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal
        b b (by simpa [B] using hv0B)]
      exact hbb
    have heq : B.filter (fun y ↦ K.Adj (v 0) y) =
        componentNeighborFinset K H b (v 0) := by
      ext y
      simp [B, H, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hsame₁ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (u j).1 = s (u 0).1 ∧ N₁ 0 j = 1).card = k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (u j).1 = s (u 0).1 ∧ N₁ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (u j).1 = s (u 0).1 ∧ K.Adj (u 0) (u j)) by
      ext j; simp [N₁, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support K A u huinj hurangeA
      (fun x : c.supp ↦ s x.1) 0]
    exact hA (u 0) hu0A
  have hsame₂ : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (v j).1 = s (v 0).1 ∧ N₂ 0 j = 1).card = k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (v 0).1 ∧ N₂ 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (v j).1 = s (v 0).1 ∧ K.Adj (v 0) (v j)) by
      ext j; simp [N₂, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) 0]
    exact hB (v 0) hv0B
  let M : Matrix (ZMod 8) (ZMod 8) ℤ :=
    fun i j ↦ K.adjMatrix ℤ (u i) (v j)
  have hMrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      M 0 j = 1).card = r := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_adj_card_eq_support_from K B v hvinj hvrangeB (u 0)]
    have hqcard : (componentNeighborFinset K H b (u 0)).card = r := by
      rw [← componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal
        a b (by simpa [A] using hu0A)]
      exact habq
    have heq : B.filter (fun y ↦ K.Adj (u 0) y) =
        componentNeighborFinset K H b (u 0) := by
      ext y
      simp [B, H, componentNeighborFinset, SimpleGraph.mem_neighborFinset,
        and_comm]
    rw [heq]
    exact hqcard
  have hMsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      s (v j).1 = s (u 0).1 ∧ M 0 j = 1).card = 3 - k := by
    rw [show ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        s (v j).1 = s (u 0).1 ∧ M 0 j = 1) =
        ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          s (v j).1 = s (u 0).1 ∧ K.Adj (u 0) (v j)) by
      ext j; simp [M, SimpleGraph.adjMatrix_apply]]
    rw [coordinate_sameSign_adj_card_eq_support_from K B v hvinj hvrangeB
      (fun x : c.supp ↦ s x.1) (u 0)]
    exact hcrossA (u 0) hu0A
  have hAfull := sizeTwo_internal_full_sum_of_filtered G c s hs_out hH
  have flip_of_coordinates
      (w : ZMod 8 → c.supp)
      (hw : ∀ z, H.neighborFinset (w z) = {w (z - 1), w (z + 1)}) :
      ∀ i, s (w (i + 1)).1 = -s (w i).1 := by
    intro i
    have hadj : H.Adj (w i) (w (i + 1)) := by
      rw [← H.mem_neighborFinset, hw]
      simp
    have hmem : (w (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (w i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (w (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (w i).2).2 _ hmem
  have hk1 : k ≤ 1 := by
    by_contra hnot
    have hkge2 : 2 ≤ k := by omega
    obtain ⟨_k', _r', _hk', _hr2', _hr7', hnf⟩ :=
      orderSixtyFour_sizeTwo_muNegOne_eightEight_signed_normalForm
        G hfree hreg hcard c hc s hs_out hs_in hH hD a b hab
          u v huinj hvinj hurange hvrange hu hv
    rcases hnf with ⟨_hk0, hrowsA, _hrowsB⟩ |
        ⟨_hk1, hrowsA, _hrowsB⟩
    · have hc0 := hcrossA (u 0) hu0A
      have hn := hrowsA (u 0) (by simpa [A] using hu0A)
      have hn' : (B.filter fun y ↦
          K.Adj (u 0) y ∧ s y.1 = s (u 0).1).card = 3 := by
        simpa [B, K] using hn
      rw [hc0] at hn'
      omega
    · have hc0 := hcrossA (u 0) hu0A
      have hn := hrowsA (u 0) (by simpa [A] using hu0A)
      have hn' : (B.filter fun y ↦
          K.Adj (u 0) y ∧ s y.1 = s (u 0).1).card = 2 := by
        simpa [B, K] using hn
      rw [hc0] at hn'
      omega
  have hbounds := alternating_C8_internal_cross_parameter_bounds_three N₁ M
    (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r hk
    (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
    (flip_of_coordinates u hu) (flip_of_coordinates v hv)
    hrow₁ hsame₁ hMrow hMsame
  have hgrid := alternating_C8_twoShore_sector_parameter_grid_muNegOne N₁ N₂
    (fun i ↦ s (u i).1) (fun i ↦ s (v i).1) k r
    (fun i ↦ hs_in _ (u i).2) (fun i ↦ hs_in _ (v i).2)
    (flip_of_coordinates u hu) (flip_of_coordinates v hv)
    hrow₁ hrow₂ hsame₁ hsame₂ hsector₁ hsector₂
  exact ⟨k, r, hk1, hr2, hr7, hbounds.1, hbounds.2.1,
    ha8, hb8, haa, habq, hbaq, hbb, hA, hB, hcrossA, hcrossB,
    hsector₁, hsector₂, hgrid⟩

end


end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegOne_eightEight_alignedLedger
