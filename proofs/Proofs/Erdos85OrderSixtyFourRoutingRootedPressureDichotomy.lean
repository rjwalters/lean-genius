import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowPatternPressure
import Proofs.Erdos85OrderSixtyFourRoutingCensusTraceDichotomy

/-! # Routing dichotomy with rooted mixed-owner pressure -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Uniform rooted pattern pressure for every ordered triple of distinct
owner colors. -/
def orderSixtyFourRootedMixedOwnerPatternPressure
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent] : Prop :=
  ∀ a b c : (secondOrderDefectGraph G).ConnectedComponent,
    a ≠ b → a ≠ c → b ≠ c → ∀ x : Fin 64,
    20 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 3).card ∨
    20 ≤ (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 4).card

/-- Top-level order-64 routing terminal: either an owner rainbow occurs, or
the exact-two-lift branch carries uniform rooted component-pattern pressure. -/
theorem orderSixtyFour_regular_fourComponents_rainbow_or_rootedPressure_and_all_two_lifts
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
    (orderSixtyFourRootedMixedOwnerPatternPressure G ∧
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
    apply orderSixtyFour_regular_fourComponents_noRainbow_large_pattern_three_or_four
      G hfree hreg hcount a b c hab hac hbc
    rintro ⟨d, hd⟩
    exact hrainbow ⟨c, d, a, b, hac.symm, hab, hbc.symm, hd⟩

end

end Erdos85
