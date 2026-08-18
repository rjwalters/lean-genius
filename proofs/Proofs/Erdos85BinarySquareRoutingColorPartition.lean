import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity

/-! # Routing colors partition every cross-component row -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Endpoints in `target` whose unique two-step route from `x` has the
prescribed intermediate component `color`. -/
def routingColorRow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) (x : source.supp)
    (color : (secondOrderDefectGraph G).ConnectedComponent) :
    Finset target.supp :=
  (Finset.univ : Finset target.supp).filter fun z =>
    color = crossIntermediateComponent G hfree hst x z

/-- Different intermediate components give disjoint endpoint rows. -/
theorem routingColorRow_disjoint_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) (x : source.supp)
    {c d : (secondOrderDefectGraph G).ConnectedComponent} (hcd : c ≠ d) :
    Disjoint (routingColorRow G hfree hst x c)
      (routingColorRow G hfree hst x d) := by
  classical
  rw [Finset.disjoint_left]
  intro z hzc hzd
  have hc := (Finset.mem_filter.mp hzc).2
  have hd := (Finset.mem_filter.mp hzd).2
  exact hcd (hc.trans hd.symm)

/-- Every target endpoint has exactly one routing color, so the color rows
cover the target component. -/
theorem biUnion_routingColorRow_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) (x : source.supp) :
    (Finset.univ.biUnion fun c => routingColorRow G hfree hst x c) =
      (Finset.univ : Finset target.supp) := by
  classical
  ext z
  simp [routingColorRow]

/-- In the order-sixty-four all-sixteen branch, every color class in this
partition has exactly four endpoints. -/
theorem orderSixtyFour_routingColorRow_card_eq_four
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (hsize : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d.supp.ncard = 16)
    {source target : (secondOrderDefectGraph G).ConnectedComponent}
    (hst : source ≠ target) (x : source.supp)
    (color : (secondOrderDefectGraph G).ConnectedComponent) :
    (routingColorRow G hfree hst x color).card = 4 := by
  apply binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
    G hfree (q := 8) (by omega) hreg (by decide)
      source color target hst
  · simpa using hsize source
  · simpa using hsize color
  · simpa using hsize target

end

end Erdos85
