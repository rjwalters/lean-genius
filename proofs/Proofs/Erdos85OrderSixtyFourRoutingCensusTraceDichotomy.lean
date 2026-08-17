import Proofs.Erdos85BinarySquareMixedOwnerRainbowBridge

/-! # Combined routing and mixed-trace census dichotomy at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component order-64 branch, either an owner-color rainbow
already occurs, or both remaining rigidities hold simultaneously: every
direct routing edge has exactly two lifts through every third component, and
all `3584` mixed-owner triangles for every three distinct colors are
cross-component. -/
theorem orderSixtyFour_regular_fourComponents_rainbow_or_crossCensus_and_all_two_lifts
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
    ((∀ a b c : (secondOrderDefectGraph G).ConnectedComponent,
      a ≠ b → a ≠ c → b ≠ c →
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c)).card = 3584) ∧
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
    have hall := orderSixtyFour_regular_fourComponents_rainbow_or_all_direct_two_lifts
      G hfree hreg hcount
    have hallTwo := hall.resolve_left hrainbow
    refine ⟨?_, hallTwo⟩
    intro a b c hab hac hbc
    let D := secondOrderDefectGraph G
    let A := componentOwnerGraph G D a
    let B := componentOwnerGraph G D b
    let C := componentOwnerGraph G D c
    have hnoLocal : ¬ ∃ d : D.ConnectedComponent,
        routingOwnerRainbow G d a b c := by
      rintro ⟨d, hd⟩
      exact hrainbow ⟨c, d, a, b, hac.symm, hab, hbc.symm, hd⟩
    have hnotNonempty :
        ¬ (sameComponentCyclicColoredTriples D A B C).Nonempty := by
      intro hnonempty
      exact hnoLocal
        ((sameComponent_mixedOwnerTriangles_nonempty_iff_exists_routingOwnerRainbow
          G a b c).mp hnonempty)
    have hempty : sameComponentCyclicColoredTriples D A B C = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hnotNonempty
    have hsplit := orderSixtyFour_regular_fourComponents_mixedOwner_componentSplit
      G hfree hreg hcount a b c hab hac hbc
    change (sameComponentCyclicColoredTriples D A B C).card +
      (crossComponentCyclicColoredTriples D A B C).card = 3584 at hsplit
    rw [hempty, Finset.card_empty, zero_add] at hsplit
    exact hsplit

end

end Erdos85
