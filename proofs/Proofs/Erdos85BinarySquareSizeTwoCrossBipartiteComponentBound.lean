import Proofs.Erdos85BinarySquareSizeTwoCrossBipartiteGirth

/-! # Number of cycles in an off-diagonal size-two cross block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Since every off-diagonal cross-block cycle has at least six vertices and
the whole bipartite block has `4q` vertices, six times the number of cycles is
at most `4q`. -/
theorem binarySquare_regular_twoSizeTwoParts_six_mul_crossComponent_card_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2) :
    6 * Fintype.card (componentCrossBipartiteGraph G c d).ConnectedComponent ≤
      4 * q := by
  let H := componentCrossBipartiteGraph G c d
  letI : DecidableEq H.ConnectedComponent := Classical.decEq _
  have hsix : ∀ e : H.ConnectedComponent, 6 ≤ e.supp.ncard :=
    binarySquare_regular_twoSizeTwoParts_crossBipartiteComponent_six_le
      G hfree hq hreg hcard c d hcd hc hd
  have hlower :
      (∑ e : H.ConnectedComponent, 6) ≤
        ∑ e : H.ConnectedComponent, e.supp.ncard := by
    exact Finset.sum_le_sum fun e _he => hsix e
  have hcardc : Fintype.card c.supp = c.supp.ncard := by
    simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
  have hcardd : Fintype.card d.supp = d.supp.ncard := by
    simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq d.supp
  have hsum : (∑ e : H.ConnectedComponent, e.supp.ncard) = 4 * q := by
    calc
      (∑ e : H.ConnectedComponent, e.supp.ncard) =
          Fintype.card (c.supp ⊕ d.supp) :=
        sum_connectedComponent_supp_ncard H
      _ = Fintype.card c.supp + Fintype.card d.supp := Fintype.card_sum
      _ = c.supp.ncard + d.supp.ncard := by rw [hcardc, hcardd]
      _ = 4 * q := by omega
  rw [hsum] at hlower
  simp [Finset.sum_const, Finset.card_univ] at hlower
  change 6 * Fintype.card H.ConnectedComponent ≤ 4 * q
  omega

/-- At order 64 (`q=8`), every off-diagonal block between size-two defect
components is a union of at most five bipartite cycles. -/
theorem orderSixtyFour_regular_twoSizeTwoParts_crossComponent_card_le_five
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (hc : c.supp.ncard = 16) (hd : d.supp.ncard = 16) :
    Fintype.card (componentCrossBipartiteGraph G c d).ConnectedComponent ≤ 5 := by
  have hbound :=
    binarySquare_regular_twoSizeTwoParts_six_mul_crossComponent_card_le
      G hfree (by omega) hreg (by decide) c d hcd (by omega) (by omega)
  omega

end

end Erdos85
