import Proofs.Erdos85BinarySquareSizeTwoOwnerLineGraph
import Proofs.Erdos85RegularTwoFoldOrderOpenWedge

/-!
# Edge regularity obstruction for size-two owner colors

This begins the direct combinatorial route from the selector-line-graph model
to adjacent-codegree irregularity.  The first graph-specific step records an
open wedge in every normalized size-two selector graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The selector graph of a normalized size-two defect component contains
two incident selector edges whose other endpoints are not joined. -/
theorem binarySquare_regular_sizeTwoSelectorGraph_exists_open_wedge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) :
    let S := sizeTwoSelectorGraph G (secondOrderDefectGraph G) c
    ∃ u v w, S.Adj u v ∧ S.Adj u w ∧ v ≠ w ∧ ¬ S.Adj v w := by
  let S := sizeTwoSelectorGraph G (secondOrderDefectGraph G) c
  have hcardSupp : Fintype.card c.supp = q * 2 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = q * 2 := hc
  exact regular_two_mul_order_exists_open_wedge S (by omega) hcardSupp
    (binarySquare_regular_sizeTwoSelectorGraph_degree
      G hfree hq hreg hcard c hc)

#print axioms binarySquare_regular_sizeTwoSelectorGraph_exists_open_wedge

end

end Erdos85
