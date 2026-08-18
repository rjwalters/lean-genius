import Proofs.Erdos85BinarySquareMixedOwnerRootedRoutingCycles
import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowPatternFour
import Proofs.Erdos85OrderSixtyFourRoutingCensusTraceDichotomy

/-! # Routing-cycle pressure in the no-owner-rainbow branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The no-rainbow pattern-four lower bound is exactly a lower bound on
all-distinct routing cycles. -/
theorem orderSixtyFour_regular_fourComponents_noRainbow_rootedRoutingCycles_card_ge_sixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hno : ¬ ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      routingOwnerRainbow G d a b c)
    (x : Fin 64) :
    16 ≤ (rootedAllDistinctRoutingCyclePairs G hfree a b c x).card := by
  rw [← rootedPattern_four_eq_rootedAllDistinctRoutingCyclePairs]
  exact orderSixtyFour_regular_fourComponents_noRainbow_patternFour_card_ge_sixteen
    G hfree hreg hcount a b c hab hac hbc hno x

/-- Uniform abundance of rooted routing cycles for every ordered triple of
distinct routing colors. -/
def orderSixtyFourNoRainbowRoutingCyclePressure
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G) : Prop :=
  ∀ a b c : (secondOrderDefectGraph G).ConnectedComponent,
    a ≠ b → a ≠ c → b ≠ c → ∀ x : Fin 64,
      16 ≤ (rootedAllDistinctRoutingCyclePairs G hfree a b c x).card

/-- Top-level terminal for the four-component branch: either an owner
rainbow occurs, or exact-two-lift routing coexists with at least sixteen
all-distinct `(a,b,c)` routing cycles at every root and every distinct color
triple. -/
theorem orderSixtyFour_regular_fourComponents_rainbow_or_routingCyclePressure_and_all_two_lifts
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4) :
    (∃ c d e f : (secondOrderDefectGraph G).ConnectedComponent,
      c ≠ e ∧ e ≠ f ∧ c ≠ f ∧ routingOwnerRainbow G d e f c) ∨
    (orderSixtyFourNoRainbowRoutingCyclePressure G hfree ∧
    (∀ c d e f : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2)) := by
  classical
  by_cases hrainbow : ∃ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      c ≠ e ∧ e ≠ f ∧ c ≠ f ∧ routingOwnerRainbow G d e f c
  · exact Or.inl hrainbow
  · right
    have hterminal :=
      orderSixtyFour_regular_fourComponents_rainbow_or_crossCensus_and_all_two_lifts
        G hfree hreg hcount
    have hterminal' := hterminal.resolve_left hrainbow
    refine ⟨?_, hterminal'.2⟩
    intro a b c hab hac hbc x
    apply orderSixtyFour_regular_fourComponents_noRainbow_rootedRoutingCycles_card_ge_sixteen
      G hfree hreg hcount a b c hab hac hbc
    rintro ⟨d, hd⟩
    exact hrainbow ⟨c, d, a, b, hac.symm, hab, hbc.symm, hd⟩

end

end Erdos85
