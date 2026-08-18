import Proofs.Erdos85DefectComponentBlockCommute
import Proofs.Erdos85OrderSixtyFourSixteenBlockCycles

/-! # The commuting H16 cycle and defect blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-component order-64 branch, the distinguished sixteen-point
defect component carries a two-regular ambient block which commutes, over
`ℂ`, with the induced seven-regular defect block. -/
theorem orderSixtyFour_seven_defect_components_sixteenBlock_commute
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      (∀ x : c.supp, (G.induce c.supp).degree x = 2) ∧
      (G.induce c.supp).adjMatrix ℂ *
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ =
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ *
          (G.induce c.supp).adjMatrix ℂ := by
  classical
  obtain ⟨c, hc16, htwo⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  refine ⟨c, hc16, htwo, ?_⟩
  exact adjMatrix_comm_secondOrderDefect_induce_component_of_regular_complex
    G hfree hreg c

end

end Erdos85
