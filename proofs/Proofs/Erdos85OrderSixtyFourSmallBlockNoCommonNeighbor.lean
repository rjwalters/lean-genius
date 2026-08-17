import Proofs.Erdos85CrossDefectComponentCommonNeighbor
import Proofs.Erdos85OrderSixtyFourSizeEightDefectClique

/-! # No common neighbors inside a small order-64 defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Distinct vertices in an order-eight component of the order-64 defect
have no common neighbor in the original graph. -/
theorem orderSixtyFour_sizeEight_defect_component_common_card_eq_zero
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he8 : e.supp.ncard = 8) (x y : e.supp) (hxy : x ≠ y) :
    (G.neighborFinset x.1 ∩ G.neighborFinset y.1).card = 0 := by
  let D := secondOrderDefectGraph G
  have hx : D.connectedComponentMk x.1 = e :=
    (ConnectedComponent.mem_supp_iff e x.1).mp x.2
  have hy : D.connectedComponentMk y.1 = e :=
    (ConnectedComponent.mem_supp_iff e y.1).mp y.2
  have hxy' : x.1 ≠ y.1 := by
    intro h
    apply hxy
    exact Subtype.ext h
  have hAdj : D.Adj x.1 y.1 :=
    orderSixtyFour_sizeEight_defect_component_adj
      G hfree hmin hcover e he8 hx hy hxy'
  rw [card_common_eq_if_secondOrderDefect G hfree x.1 y.1 hxy']
  simp [D, hAdj]

/-- Logical form of the zero-common-neighbor law inside a small block. -/
theorem orderSixtyFour_sizeEight_defect_component_no_common_neighbor
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (e : (secondOrderDefectGraph G).ConnectedComponent)
    (he8 : e.supp.ncard = 8) (x y : e.supp) (hxy : x ≠ y) :
    ¬ ∃ z : Fin 64, G.Adj x.1 z ∧ G.Adj y.1 z := by
  intro h
  obtain ⟨z, hxz, hyz⟩ := h
  have hz : z ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x.1 z).mpr hxz,
        (G.mem_neighborFinset y.1 z).mpr hyz⟩
  have hzero :=
    orderSixtyFour_sizeEight_defect_component_common_card_eq_zero
      G hfree hmin hcover e he8 x y hxy
  rw [Finset.card_eq_zero.mp hzero] at hz
  simpa using hz

end

end Erdos85
