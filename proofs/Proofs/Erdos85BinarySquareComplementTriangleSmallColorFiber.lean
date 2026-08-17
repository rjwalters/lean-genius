import Proofs.Erdos85BinarySquareComplementTriangleColorPartition

/-! # A small restricted-owner color fiber at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The `672` ordered component-complement triangle budget is spread across
`4³ = 64` ordered owner-color fibers.  Consequently at least one fiber has
cardinality at most `10`. -/
theorem orderSixtyFour_exists_restrictedOwner_cyclicTriples_card_le_ten
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    ∃ colors :
        (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent,
      (cyclicColoredTriples
        (restrictedComponentOwnerGraph G d colors.1)
        (restrictedComponentOwnerGraph G d colors.2.2)
        (restrictedComponentOwnerGraph G d colors.2.1)).card ≤ 10 := by
  classical
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let fiber : C × C × C → ℕ := fun colors =>
    (cyclicColoredTriples
      (restrictedComponentOwnerGraph G d colors.1)
      (restrictedComponentOwnerGraph G d colors.2.2)
      (restrictedComponentOwnerGraph G d colors.2.1)).card
  have hbudget : (∑ colors : C × C × C, fiber colors) ≤ 672 := by
    simpa [C, fiber] using
      orderSixtyFour_sum_card_restrictedOwner_cyclicTriples_le_672
        G hfree hreg hcount d
  by_contra hsmall
  push Not at hsmall
  have hlarge : ∀ colors : C × C × C, 11 ≤ fiber colors := by
    intro colors
    have h : ¬ fiber colors ≤ 10 := by
      simpa [fiber] using hsmall colors
    omega
  have hlower : 704 ≤ ∑ colors : C × C × C, fiber colors := by
    calc
      704 = ∑ _colors : C × C × C, 11 := by
        simp [C, hcount]
      _ ≤ ∑ colors : C × C × C, fiber colors := by
        exact Finset.sum_le_sum fun colors _ => hlarge colors
  omega

end

end Erdos85
