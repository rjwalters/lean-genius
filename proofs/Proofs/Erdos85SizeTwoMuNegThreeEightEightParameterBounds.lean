import Proofs.Erdos85SizeTwoMuNegThreeEightEightCrossSameMatching

/-! # Signed capacity bounds for the `mu=-3` C8+C8 quotient -/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- Every sign class, and its complement, has cardinality four on an
alternating signed C8. -/
theorem zmodEight_alternating_sign_class_cards_four
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (t : ℤ) (ht : t = -1 ∨ t = 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ f i = t).card = 4 ∧
    ((Finset.univ : Finset (ZMod 8)).filter fun i ↦ f i ≠ t).card = 4 := by
  classical
  obtain ⟨hsame, hopp⟩ := zmodEight_alternating_sign_filter_cards
    f hsign hflip
  have htcard : ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
      f i = t).card = 4 := by
    rcases ht with rfl | rfl <;> rcases hsign 0 with h0 | h0
    · simpa [h0] using hsame
    · simpa [h0] using hopp
    · simpa [h0] using hopp
    · simpa [h0] using hsame
  constructor
  · exact htcard
  · have hpart := Finset.card_filter_add_card_filter_not
      (fun i : ZMod 8 ↦ f i = t) (s := Finset.univ)
    rw [htcard, show (Finset.univ : Finset (ZMod 8)).card = 8 by decide] at hpart
    have hn : ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        ¬ f i = t).card = 4 := by omega
    simpa only [ne_eq] using hn

/-- A binary row on an alternating C8 has at most four entries outside any
fixed sign class. -/
theorem binary_C8_row_card_le_same_add_four
    (M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f : ZMod 8 → ℤ)
    (hsign : ∀ i, f i = -1 ∨ f i = 1)
    (hflip : ∀ i, f (i + 1) = -f i)
    (x : ZMod 8) (t : ℤ) (ht : t = -1 ∨ t = 1) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ M x j = 1).card ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = t ∧ M x j = 1).card + 4 := by
  classical
  let T := (Finset.univ : Finset (ZMod 8)).filter fun j ↦ M x j = 1
  have hpart := Finset.card_filter_add_card_filter_not
    (fun j ↦ f j = t) (s := T)
  have hoppSub : (T.filter fun j ↦ ¬ f j = t) ⊆
      (Finset.univ : Finset (ZMod 8)).filter fun j ↦ f j ≠ t := by
    intro j hj
    have hj' := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'.2⟩
  have hoppLe : (T.filter fun j ↦ ¬ f j = t).card ≤ 4 := by
    calc
      _ ≤ ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ f j ≠ t).card :=
        Finset.card_le_card hoppSub
      _ = 4 := (zmodEight_alternating_sign_class_cards_four
        f hsign hflip t ht).2
  have hsameEq : (T.filter fun j ↦ f j = t).card =
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = t ∧ M x j = 1).card := by
    congr 1
    ext j
    simp [T, and_comm]
  have hle : T.card ≤
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        f j = t ∧ M x j = 1).card + 4 := by
    calc
      T.card = (T.filter fun j ↦ f j = t).card +
          (T.filter fun j ↦ ¬ f j = t).card := hpart.symm
      _ ≤ (T.filter fun j ↦ f j = t).card + 4 :=
        Nat.add_le_add_left hoppLe _
      _ = ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
          f j = t ∧ M x j = 1).card + 4 := by rw [hsameEq]
  simpa [T] using hle

/-- The internal and cross signed row counts force the sharp arithmetic
window `3 ≤ r+k ≤ 6`.  Thus `k=0` implies `r≥3`, `k=1` implies
`r≤5`, and `k=2` implies `r≤4`. -/
theorem alternating_C8_internal_cross_parameter_bounds
    (N M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ)
    (k r : ℕ) (hk : k ≤ 2)
    (hfsign : ∀ i, f i = -1 ∨ f i = 1)
    (hgsign : ∀ i, g i = -1 ∨ g i = 1)
    (hfflip : ∀ i, f (i + 1) = -f i)
    (hgflip : ∀ i, g (i + 1) = -g i)
    (hNrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      N 0 j = 1).card = 7 - r)
    (hNsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      f j = f 0 ∧ N 0 j = 1).card = k)
    (hMrow : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      M 0 j = 1).card = r)
    (hMsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      g j = f 0 ∧ M 0 j = 1).card = 2 - k) :
    3 ≤ r + k ∧ r + k ≤ 6 ∧
      (k = 0 → 3 ≤ r) ∧
      (k = 1 → r ≤ 5) ∧
      (k = 2 → r ≤ 4) := by
  have hNle := binary_C8_row_card_le_same_add_four
    N f hfsign hfflip 0 (f 0) (hfsign 0)
  have hMle := binary_C8_row_card_le_same_add_four
    M g hgsign hgflip 0 (f 0) (hfsign 0)
  rw [hNrow, hNsame] at hNle
  rw [hMrow, hMsame] at hMle
  omega

/-- Coordinate-card transport for an unmasked adjacency row. -/
theorem coordinate_adj_card_eq_support_from
    {X : Type*} [Fintype X] [DecidableEq X]
    (K : SimpleGraph X) [DecidableRel K.Adj]
    (A : Finset X) (u : ZMod 8 → X) (huinj : Function.Injective u)
    (hurange : Set.range u = ↑A) (x : X) :
    ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      K.Adj x (u j)).card = (A.filter fun y ↦ K.Adj x y).card := by
  classical
  apply Finset.card_bij (fun j _ ↦ u j)
  · intro j hj
    have hj' := Finset.mem_filter.mp hj
    rw [Finset.mem_filter]
    refine ⟨?_, hj'.2⟩
    change u j ∈ (↑A : Set X)
    rw [← hurange]
    exact ⟨j, rfl⟩
  · intro j₁ hj₁ j₂ hj₂ h
    exact huinj h
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyA : y ∈ (↑A : Set X) := hy'.1
    rw [← hurange] at hyA
    obtain ⟨j, rfl⟩ := hyA
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.2⟩, rfl⟩

set_option maxHeartbeats 1200000 in
/-- Graph-facing quotient bound in the normalized `mu=-3` C8+C8 branch.
The same `k` controlling both signed diagonal blocks satisfies the sharp
window `3 ≤ r+k ≤ 6` with the cross quotient `r`. -/
theorem orderSixtyFour_sizeTwo_muNegThree_eightEight_parameter_bounds
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
      {v (z - 1), v (z + 1)}) :
    ∃ k r : ℕ, k ≤ 2 ∧ 2 ≤ r ∧ r ≤ 7 ∧
      3 ≤ r + k ∧ r + k ≤ 6 ∧
      (k = 0 → 3 ≤ r) ∧ (k = 1 → r ≤ 5) ∧
      (k = 2 → r ≤ 4) := by
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
  have flip_of_coordinates
      (w : ZMod 8 → c.supp)
      (hw : ∀ z, Hc.neighborFinset (w z) = {w (z - 1), w (z + 1)}) :
      ∀ i, s (w (i + 1)).1 = -s (w i).1 := by
    intro i
    have hadj : Hc.Adj (w i) (w (i + 1)) := by
      rw [← Hc.mem_neighborFinset, hw]
      simp
    have hmem : (w (i + 1)).1 ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c (w i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj, (w (i + 1)).2⟩
    exact (internal_alternation G hfree (by omega) hreg hcard c hc s
      hs_in hs_out hAfull (w i).2).2 _ hmem
  have hbounds := alternating_C8_internal_cross_parameter_bounds N M
    (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) k r hk
    (fun i ↦ hs_in _ (u i).2) (fun j ↦ hs_in _ (v j).2)
    (flip_of_coordinates u hu) (flip_of_coordinates v hv)
    hNrow hNsame hMrow hMsame
  exact ⟨k, r, hk, hr2, hr7, hbounds⟩

end

end Erdos85

#print axioms Erdos85.alternating_C8_internal_cross_parameter_bounds
#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_eightEight_parameter_bounds
