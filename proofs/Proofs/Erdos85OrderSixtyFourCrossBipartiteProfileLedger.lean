import Proofs.Erdos85OrderSixtyFourCrossBipartiteCycleCount

/-! # Uniform cycle-profile ledger for order-64 cross blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Any family of even parts at least six and of total size 32 satisfies the
exact excess ledger `3|ι| + Σ (aᵢ-6)/2 = 16`. -/
theorem even_parts_six_le_sum_thirtyTwo_profile_ledger
    {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (heven : ∀ i, Even (a i)) (hsix : ∀ i, 6 ≤ a i)
    (hsum : (∑ i, a i) = 32) :
    (∀ i, a i = 6 + 2 * ((a i - 6) / 2)) ∧
      3 * Fintype.card ι + (∑ i, (a i - 6) / 2) = 16 := by
  have hshape : ∀ i, a i = 6 + 2 * ((a i - 6) / 2) := by
    intro i
    obtain ⟨k, hk⟩ := heven i
    have := hsix i
    omega
  have hsum' :
      (∑ i : ι, (6 + 2 * ((a i - 6) / 2))) = 32 := by
    calc
      (∑ i : ι, (6 + 2 * ((a i - 6) / 2))) = ∑ i, a i := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (hshape i).symm
      _ = 32 := hsum
  have hconst : (∑ _i : ι, (6 : ℕ)) = 6 * Fintype.card ι := by
    simp [mul_comm]
  rw [Finset.sum_add_distrib, hconst, ← Finset.mul_sum] at hsum'
  refine ⟨hshape, ?_⟩
  omega

/-- Equivalently, after fixing the number `k` of parts, their total excess is
`16-3k`. -/
theorem even_parts_six_le_sum_thirtyTwo_excess_sum_of_card
    {ι : Type*} [Fintype ι]
    (a : ι → ℕ) (heven : ∀ i, Even (a i)) (hsix : ∀ i, 6 ≤ a i)
    (hsum : (∑ i, a i) = 32) (k : ℕ) (hcard : Fintype.card ι = k) :
    (∑ i, (a i - 6) / 2) = 16 - 3 * k := by
  have hledger :=
    (even_parts_six_le_sum_thirtyTwo_profile_ledger a heven hsix hsum).2
  rw [hcard] at hledger
  omega

/-- **Uniform order-64 cross-profile ledger.** Every off-diagonal cross block
between normalized size-two components satisfies
`3·(# cycles) + Σ_C (|C|-6)/2 = 16`. -/
theorem orderSixtyFour_twoSizeTwoParts_crossBipartite_profile_ledger
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
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16) :
    (∀ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
      e.supp.ncard = 6 + 2 * ((e.supp.ncard - 6) / 2)) ∧
    3 * Fintype.card
        (componentCrossBipartiteGraph G c d).ConnectedComponent +
      (∑ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
        (e.supp.ncard - 6) / 2) = 16 := by
  let a := fun e : (componentCrossBipartiteGraph G c d).ConnectedComponent =>
    e.supp.ncard
  apply even_parts_six_le_sum_thirtyTwo_profile_ledger a
  · intro e
    exact binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_even
      G hfree (q := 8) (by omega) hreg (by omega) c d
        (by omega) (by omega) e
  · intro e
    exact binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_six_le
      G hfree (q := 8) (by omega) hreg (by omega) c d hcd
        (by omega) (by omega) e
  · exact orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_order_sum
      G c d hc hd

/-- If the cross block has exactly `k` components, its total half-length
excess is exactly `16-3k`. -/
theorem orderSixtyFour_twoSizeTwoParts_crossBipartite_excess_sum_of_card
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
    (k : ℕ)
    (hcount : Fintype.card
      (componentCrossBipartiteGraph G c d).ConnectedComponent = k) :
    (∑ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
      (e.supp.ncard - 6) / 2) = 16 - 3 * k := by
  have hledger :=
    (orderSixtyFour_twoSizeTwoParts_crossBipartite_profile_ledger
      G hfree hreg hcard c d hcd hc hd).2
  rw [hcount] at hledger
  omega

end

end Erdos85
