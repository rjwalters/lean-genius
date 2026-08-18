import Proofs.Erdos85OrderSixtyFourRoutingRainbowExcess

/-! # Reversal symmetry of routing rainbow excess -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The canonical unique common neighbor is unchanged when its endpoints are
reversed. -/
theorem crossCommonNeighbor_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    crossCommonNeighbor G hfree hce x z =
      crossCommonNeighbor G hfree hce.symm z x := by
  exact eq_crossCommonNeighbor_of_adj G hfree hce.symm z x
    ⟨(crossCommonNeighbor_spec G hfree hce x z).2,
      (crossCommonNeighbor_spec G hfree hce x z).1⟩

/-- Reversing the direct endpoint edge leaves its rainbow-excess finset
through the same third component literally unchanged. -/
theorem orderSixtyFourRoutingRainbowExcessFinset_reverse
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (k : Fin 4) (x : c.supp) (w : f.supp) :
    orderSixtyFourRoutingRainbowExcessFinset
        G hfree hcount hce hef hcf k x w =
      orderSixtyFourRoutingRainbowExcessFinset
        G hfree hcount hef.symm hce.symm hcf.symm k w x := by
  ext z
  simp only [orderSixtyFourRoutingRainbowExcessFinset,
    orderSixtyFourRoutingCompletionFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hA := orderSixtyFourRoutingArray_reverse
    G hfree hcount hce x z
  have hB := orderSixtyFourRoutingArray_reverse
    G hfree hcount hef z w
  have hY₁ := crossCommonNeighbor_reverse G hfree hce x z
  have hY₂ := crossCommonNeighbor_reverse G hfree hef z w
  have hY₃ := crossCommonNeighbor_reverse G hfree hcf x w
  rw [← hA, ← hB, ← hY₁, ← hY₂, ← hY₃]
  tauto

/-- Cardinal form of reversal symmetry. -/
theorem orderSixtyFourRoutingRainbowExcess_card_reverse
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (k : Fin 4) (x : c.supp) (w : f.supp) :
    (orderSixtyFourRoutingRainbowExcessFinset
        G hfree hcount hce hef hcf k x w).card =
      (orderSixtyFourRoutingRainbowExcessFinset
        G hfree hcount hef.symm hce.symm hcf.symm k w x).card := by
  rw [orderSixtyFourRoutingRainbowExcessFinset_reverse
    G hfree hcount hce hef hcf k x w]

end

end Erdos85
