import Proofs.Erdos85OrderSixtyFourFourTwoTwoBowtieSelectorRectangle

/-! # Exact exclusion principle for the `[4,2,2]` bowtie leaf -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Precise remaining local principle for the exceptional `[4,2,2]`
pressure pattern.  Its hypotheses include the full graph-facing binary-square
structure, not merely the locally consistent bare selector rectangle. -/
def OrderSixtyFourFourTwoTwoBowtieExclusionPrinciple : Prop :=
  ∀ (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent],
    ¬ containsC4 (Fin 64) G →
    (∀ x, G.degree x = 8) →
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent = 3 →
    ∀ (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ),
    (∀ d, d.supp.ncard = 8 * m d) →
    ∀ a b c f : (secondOrderDefectGraph G).ConnectedComponent,
    a ≠ b → a ≠ c → b ≠ c →
    m a = 2 → m b = 2 → m c = 4 → f ≠ c →
    ¬ HasOppositeThirdEdgeInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) c f

/-- Under the exact bowtie exclusion principle, the last unordered-edge
branch has the same orientation and therefore reaches the already-developed
twice-rotated repeated-closing routing terminal. -/
theorem orderSixtyFour_fourTwoTwo_unorderedClosing_forces_repeatedClosing_of_principle
    (P : OrderSixtyFourFourTwoTwoBowtieExclusionPrinciple)
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b c f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hma : m a = 2) (hmb : m b = 2) (hmc : m c = 4) (hfc : f ≠ c)
    (hblock : 219 ≤
      (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) c f c).card) :
    HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) c)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) c c f := by
  rcases orderSixtyFour_fourTwoTwo_sizeFour_unorderedClosing_dichotomy
    G hfree hreg m hm a b c f hmc hblock with hrepeat | hopp
  · exact hrepeat
  · exact (P G hfree hreg hcount m hm a b c f
      hab hac hbc hma hmb hmc hfc hopp).elim

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_fourTwoTwo_unorderedClosing_forces_repeatedClosing_of_principle
