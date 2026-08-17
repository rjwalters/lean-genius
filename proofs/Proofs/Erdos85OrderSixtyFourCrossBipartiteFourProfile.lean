import Proofs.Erdos85OrderSixtyFourCrossBipartiteCycleCount

/-! # The four-cycle profile of an order-64 cross block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Four even natural numbers, each at least six and summing to 32, are
obtained from four nonnegative excesses summing to four via `aᵢ=6+2eᵢ`.
This is the compact composition form of the five possible partitions. -/
theorem four_even_parts_six_le_sum_thirtyTwo_excess_partition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (hcard : Fintype.card ι = 4)
    (heven : ∀ i, Even (a i)) (hsix : ∀ i, 6 ≤ a i)
    (hsum : (∑ i, a i) = 32) :
    (∀ i, a i = 6 + 2 * ((a i - 6) / 2)) ∧
      (∑ i, (a i - 6) / 2) = 4 ∧
      ∀ i, (a i - 6) / 2 ≤ 4 := by
  have hupper : ∀ i, a i ≤ 14 := by
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
  have hshape : ∀ i, a i = 6 + 2 * ((a i - 6) / 2) := by
    intro i
    obtain ⟨k, hk⟩ := heven i
    have := hsix i
    omega
  have hexcess : (∑ i, (a i - 6) / 2) = 4 := by
    have hsum' : (∑ i : ι, (6 + 2 * ((a i - 6) / 2))) = 32 := by
      calc
        (∑ i : ι, (6 + 2 * ((a i - 6) / 2))) = ∑ i, a i := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact (hshape i).symm
        _ = 32 := hsum
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      hcard] at hsum'
    rw [← Finset.mul_sum] at hsum'
    simp only [nsmul_eq_mul] at hsum'
    omega
  refine ⟨hshape, hexcess, ?_⟩
  intro i
  have := hupper i
  omega

/-- Consequently every part has one of the five possible even orders between
six and fourteen. -/
theorem four_even_parts_six_le_sum_thirtyTwo_values
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (hcard : Fintype.card ι = 4)
    (heven : ∀ i, Even (a i)) (hsix : ∀ i, 6 ≤ a i)
    (hsum : (∑ i, a i) = 32) :
    ∀ i, a i = 6 ∨ a i = 8 ∨ a i = 10 ∨ a i = 12 ∨ a i = 14 := by
  obtain ⟨hshape, _hsumExcess, hle⟩ :=
    four_even_parts_six_le_sum_thirtyTwo_excess_partition
      a hcard heven hsix hsum
  intro i
  have := hshape i
  have := hle i
  omega

/-- If an order-64 cross block has four connected components, their even
orders are `6+2e` for four excesses summing exactly to four. -/
theorem orderSixtyFour_twoSizeTwoParts_crossBipartite_fourComponent_profile
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
    (hfour : Fintype.card
      (componentCrossBipartiteGraph G c d).ConnectedComponent = 4) :
    (∀ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
      e.supp.ncard = 6 + 2 * ((e.supp.ncard - 6) / 2)) ∧
    (∑ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
      (e.supp.ncard - 6) / 2) = 4 ∧
    ∀ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
      e.supp.ncard = 6 ∨ e.supp.ncard = 8 ∨ e.supp.ncard = 10 ∨
        e.supp.ncard = 12 ∨ e.supp.ncard = 14 := by
  classical
  let a := fun e : (componentCrossBipartiteGraph G c d).ConnectedComponent =>
    e.supp.ncard
  have heven : ∀ e, Even (a e) := fun e =>
    binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_even
      G hfree (q := 8) (by omega) hreg (by omega) c d (by omega) (by omega) e
  have hsix : ∀ e, 6 ≤ a e := fun e =>
    binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_six_le
      G hfree (q := 8) (by omega) hreg (by omega) c d hcd
        (by omega) (by omega) e
  have hsum : (∑ e, a e) = 32 :=
    orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_order_sum
      G c d hc hd
  obtain ⟨hshape, hexcess, _hle⟩ :=
    four_even_parts_six_le_sum_thirtyTwo_excess_partition
      a hfour heven hsix hsum
  refine ⟨hshape, hexcess, ?_⟩
  exact four_even_parts_six_le_sum_thirtyTwo_values
    a hfour heven hsix hsum

end

end Erdos85
