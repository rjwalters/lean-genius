import Proofs.Erdos85OrderSixtyFourThreeComponentCrossBudget
import Proofs.Erdos85BinarySquareThreeComponentPatternPressure

/-! # Graph-facing pressure package for the order-64 three-component strata -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A regular C4-free order-64 graph with three defect components supplies
either the `[4,2,2]` pressure package (a nonlocal block of size at least 219)
or the `[3,3,2]` package (a nonlocal block of size at least 253). -/
theorem orderSixtyFour_regular_threeComponents_patternPressure
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 3) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ d, d.supp.ncard = 8 * m d) ∧
      ((∃ a b c e f g : (secondOrderDefectGraph G).ConnectedComponent,
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          m a = 2 ∧ m b = 2 ∧ m c = 4 ∧
          ¬ (e = f ∧ f = g) ∧
          219 ≤
            (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
              (componentOwnerGraph G (secondOrderDefectGraph G) a)
              (componentOwnerGraph G (secondOrderDefectGraph G) b)
              (componentOwnerGraph G (secondOrderDefectGraph G) c)
              e f g).card) ∨
       (∃ a b c e f g : (secondOrderDefectGraph G).ConnectedComponent,
          a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          m a = 2 ∧ m b = 3 ∧ m c = 3 ∧
          ¬ (e = f ∧ f = g) ∧
          253 ≤
            (cyclicColoredTriplesInBlocks (secondOrderDefectGraph G)
              (componentOwnerGraph G (secondOrderDefectGraph G) a)
              (componentOwnerGraph G (secondOrderDefectGraph G) b)
              (componentOwnerGraph G (secondOrderDefectGraph G) c)
              e f g).card)) := by
  obtain ⟨m, hm, hshape⟩ :=
    orderSixtyFour_regular_threeComponents_crossBudget
      G hfree hreg hcount
  refine ⟨m, hm, ?_⟩
  rcases hshape with h422 | h332
  · left
    obtain ⟨a, b, c, hab, hac, hbc, hma, hmb, hmc, hcross⟩ := h422
    obtain ⟨e, f, g, hnonlocal, hblock⟩ :=
      threeComponents_exists_cross_componentBlock_card_ge_219
        (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        hcount hcross
    exact ⟨a, b, c, e, f, g, hab, hac, hbc,
      hma, hmb, hmc, hnonlocal, hblock⟩
  · right
    obtain ⟨a, b, c, hab, hac, hbc, hma, hmb, hmc, hcross⟩ := h332
    obtain ⟨e, f, g, hnonlocal, hblock⟩ :=
      threeComponents_exists_cross_componentBlock_card_ge_253
        (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)
        hcount hcross
    exact ⟨a, b, c, e, f, g, hab, hac, hbc,
      hma, hmb, hmc, hnonlocal, hblock⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_threeComponents_patternPressure
