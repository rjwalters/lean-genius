import Proofs.Erdos85OrderSixtyFourCrossBipartiteCycleCount

/-! # The five-cycle profile of an order-64 cross block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Five even natural numbers, each at least six and summing to 32, consist
of one eight and four sixes. -/
theorem five_even_parts_six_le_sum_thirtyTwo
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (hcard : Fintype.card ι = 5)
    (heven : ∀ i, Even (a i)) (hsix : ∀ i, 6 ≤ a i)
    (hsum : (∑ i, a i) = 32) :
    (Finset.univ.filter fun i => a i = 8).card = 1 ∧
      ∀ i, a i = 6 ∨ a i = 8 := by
  have hupper : ∀ i, a i ≤ 8 := by
    intro i
    have hrest : 6 * (Fintype.card ι - 1) ≤
        ∑ j ∈ (Finset.univ.erase i), a j := by
      calc
        6 * (Fintype.card ι - 1) =
            ∑ _j ∈ (Finset.univ.erase i), 6 := by
              simp [Finset.card_erase_of_mem, hcard, mul_comm]
        _ ≤ ∑ j ∈ (Finset.univ.erase i), a j := by
          apply Finset.sum_le_sum
          intro j _hj
          exact hsix j
    have hsplit := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
    rw [hsum] at hsplit
    omega
  have hshape : ∀ i, a i = 6 ∨ a i = 8 := by
    intro i
    obtain ⟨k, hk⟩ := heven i
    have := hsix i
    have := hupper i
    omega
  let S := Finset.univ.filter fun i => a i = 8
  have hSne : S.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hall : ∀ i, a i = 6 := by
      intro i
      rcases hshape i with hi | hi
      · exact hi
      · exfalso
        have : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        rw [hempty] at this
        simp at this
    have : (∑ i, a i) = 6 * Fintype.card ι := by
      simp_rw [hall]
      simp [mul_comm]
    omega
  have hSle : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    have hai : a i = 8 := (Finset.mem_filter.mp hi).2
    have haj : a j = 8 := (Finset.mem_filter.mp hj).2
    have hjmem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩
    have hcardEraseI : (Finset.univ.erase i).card = 4 := by
      simp [hcard]
    have hcardEraseIJ : ((Finset.univ.erase i).erase j).card = 3 := by
      rw [Finset.card_erase_of_mem hjmem, hcardEraseI]
    have hrest : 6 * (Fintype.card ι - 2) ≤
        ∑ k ∈ ((Finset.univ.erase i).erase j), a k := by
      calc
        6 * (Fintype.card ι - 2) =
            ∑ _k ∈ ((Finset.univ.erase i).erase j), 6 := by
              simp [hcard, hcardEraseIJ, mul_comm]
        _ ≤ ∑ k ∈ ((Finset.univ.erase i).erase j), a k := by
          apply Finset.sum_le_sum
          intro k _hk
          exact hsix k
    have hsplitI := Finset.add_sum_erase Finset.univ a (Finset.mem_univ i)
    have hsplitJ := Finset.add_sum_erase (Finset.univ.erase i) a hjmem
    rw [hsum, hai] at hsplitI
    rw [haj] at hsplitJ
    omega
  exact ⟨Nat.le_antisymm hSle (Finset.one_le_card.mpr hSne), hshape⟩

/-- If an order-64 cross block has five connected components, exactly one
has order eight and all the others have order six. -/
theorem orderSixtyFour_twoSizeTwoParts_crossBipartite_fiveComponent_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16)
    (hfive : Fintype.card
      (componentCrossBipartiteGraph G c d).ConnectedComponent = 5) :
    (Finset.univ.filter fun e :
      (componentCrossBipartiteGraph G c d).ConnectedComponent =>
        e.supp.ncard = 8).card = 1 ∧
      ∀ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
        e.supp.ncard = 6 ∨ e.supp.ncard = 8 := by
  classical
  apply five_even_parts_six_le_sum_thirtyTwo
  · exact hfive
  · intro e
    exact binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_even
      G hfree (q := 8) (by omega) hreg (by omega) c d (by omega) (by omega) e
  · intro e
    exact binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_six_le
      G hfree (q := 8) (by omega) hreg (by omega) c d hcd (by omega) (by omega) e
  · exact orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_order_sum
      G c d hc hd

end

end Erdos85
