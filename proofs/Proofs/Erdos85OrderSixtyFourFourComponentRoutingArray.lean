import Proofs.Erdos85BinarySquareSizeTwoRoutingRegularity

/-! # Balanced routing arrays in the four-component order-64 branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Endpoints in `e` whose unique route from `x` uses component `d`. -/
def crossRoutingColorClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (x : c.supp) (d : (secondOrderDefectGraph G).ConnectedComponent) :
    Finset e.supp :=
  Finset.univ.filter fun z => d = crossIntermediateComponent G hfree hce x z

/-- Every routing color occurs exactly four times in each endpoint row. -/
theorem orderSixtyFour_fourSizeSixteenComponents_routingColorClass_card_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 64)
    (hparts : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d.supp.ncard = 16)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (x : c.supp) (d : (secondOrderDefectGraph G).ConnectedComponent) :
    (crossRoutingColorClass G hfree c e hce x d).card = 4 := by
  exact binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four
    G hfree (q := 8) (by omega) hreg (by omega) c d e hce
      (by simpa using hparts c) (by simpa using hparts d)
      (by simpa using hparts e) x

/-- Distinct routing colors have disjoint endpoint classes. -/
theorem crossRoutingColorClass_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (x : c.supp) {d₁ d₂ : (secondOrderDefectGraph G).ConnectedComponent}
    (hdd : d₁ ≠ d₂) :
    Disjoint (crossRoutingColorClass G hfree c e hce x d₁)
      (crossRoutingColorClass G hfree c e hce x d₂) := by
  rw [Finset.disjoint_left]
  intro z hz₁ hz₂
  have h₁ := (Finset.mem_filter.mp hz₁).2
  have h₂ := (Finset.mem_filter.mp hz₂).2
  exact hdd (h₁.trans h₂.symm)

/-- Routing color classes exhaust the opposite endpoint component. -/
theorem crossRoutingColorClass_biUnion_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (x : c.supp) :
    Finset.univ.biUnion (crossRoutingColorClass G hfree c e hce x) =
      (Finset.univ : Finset e.supp) := by
  classical
  ext z
  simp [crossRoutingColorClass]

/-- In the maximal four-component branch the four color-class cardinalities
sum to all sixteen opposite endpoints. -/
theorem orderSixtyFour_fourSizeSixteenComponents_routingColorClass_card_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 64)
    (hcomponents : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (hparts : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      d.supp.ncard = 16)
    (c e : (secondOrderDefectGraph G).ConnectedComponent) (hce : c ≠ e)
    (x : c.supp) :
    (∑ d : (secondOrderDefectGraph G).ConnectedComponent,
      (crossRoutingColorClass G hfree c e hce x d).card) = 16 := by
  simp_rw [orderSixtyFour_fourSizeSixteenComponents_routingColorClass_card_four
    G hfree hreg hcard hparts c e hce x]
  simp [hcomponents]

end

end Erdos85
