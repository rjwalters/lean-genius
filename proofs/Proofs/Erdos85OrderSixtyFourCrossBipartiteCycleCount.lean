import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteGirth

/-! # Component-count bound for order-64 cross blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The connected-component orders of a cross graph between two order-16
defect components sum to 32. -/
theorem orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_order_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16) :
    (∑ e : (componentCrossBipartiteGraph G c d).ConnectedComponent,
      e.supp.ncard) = 32 := by
  rw [sum_connectedComponent_supp_ncard]
  rw [Fintype.card_sum]
  have hccard : Fintype.card c.supp = 16 := by
    simpa [Nat.card_eq_fintype_card] using
      (Nat.card_coe_set_eq c.supp).trans hc
  have hdcard : Fintype.card d.supp = 16 := by
    simpa [Nat.card_eq_fintype_card] using
      (Nat.card_coe_set_eq d.supp).trans hd
  rw [hccard, hdcard]

/-- At order 64, every off-diagonal cross block between normalized size-two
defect components has at most five connected cycle components. -/
theorem orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_count_le_five
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
    Fintype.card (componentCrossBipartiteGraph G c d).ConnectedComponent ≤ 5 := by
  let H := componentCrossBipartiteGraph G c d
  change Fintype.card H.ConnectedComponent ≤ 5
  have hsum : (∑ e : H.ConnectedComponent, e.supp.ncard) = 32 := by
    exact orderSixtyFour_twoSizeTwoParts_crossBipartiteComponent_order_sum
      G c d hc hd
  have hbound : 6 * Fintype.card H.ConnectedComponent ≤
      ∑ e : H.ConnectedComponent, e.supp.ncard := by
    calc
      6 * Fintype.card H.ConnectedComponent =
          ∑ _e : H.ConnectedComponent, 6 := by
            simp [Finset.sum_const, Finset.card_univ, mul_comm]
      _ ≤ ∑ e : H.ConnectedComponent, e.supp.ncard := by
        apply Finset.sum_le_sum
        intro e _he
        exact binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_six_le
          G hfree (q := 8) (by omega) hreg (by omega) c d hcd (by omega) (by omega) e
  rw [hsum] at hbound
  omega

end

end Erdos85
