import Proofs.Erdos85OrderSixtyFourRoutingCycleComponentConcentration

/-! # Concentrated routing-cycle terminal at order sixty-four -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Uniform fixed-component-pair concentration of rooted prescribed routing
cycles. -/
def orderSixtyFourNoRainbowRoutingCycleComponentPairPressure
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G) : Prop :=
  ∀ a b c : (secondOrderDefectGraph G).ConnectedComponent,
    a ≠ b → a ≠ c → b ≠ c → ∀ x : Fin 64,
      ∃ e f : (secondOrderDefectGraph G).ConnectedComponent,
        e ≠ (secondOrderDefectGraph G).connectedComponentMk x ∧
        f ≠ (secondOrderDefectGraph G).connectedComponentMk x ∧ e ≠ f ∧
        3 ≤ (rootedAllDistinctRoutingCyclePairsInComponents
          G hfree a b c e f x).card

/-- Top-level four-component terminal with the numerical cycle pressure
already concentrated into a fixed ordered pair of external components. -/
theorem orderSixtyFour_regular_fourComponents_rainbow_or_componentPairPressure_and_all_two_lifts
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
    (orderSixtyFourNoRainbowRoutingCycleComponentPairPressure G hfree ∧
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
      orderSixtyFour_regular_fourComponents_rainbow_or_routingCyclePressure_and_all_two_lifts
        G hfree hreg hcount
    have hright := hterminal.resolve_left hrainbow
    refine ⟨?_, hright.2⟩
    intro a b c hab hac hbc x
    apply
      orderSixtyFour_regular_fourComponents_noRainbow_exists_componentPair_three_routingCycles
        G hfree hreg hcount a b c hab hac hbc
    rintro ⟨d, hd⟩
    have hglobal : ∃ c d e f :
        (secondOrderDefectGraph G).ConnectedComponent,
        c ≠ e ∧ e ≠ f ∧ c ≠ f ∧ routingOwnerRainbow G d e f c :=
      ⟨c, d, a, b, hac.symm, hab, hbc.symm, hd⟩
    exact hrainbow hglobal

end

end Erdos85
