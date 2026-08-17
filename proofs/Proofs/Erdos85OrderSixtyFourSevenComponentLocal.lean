import Proofs.Erdos85OrderSixtyFourMinusOneTrace

/-! # Local ambient degrees in the seven-component order-64 branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If the defect graph has seven components, the ambient graph induced on
the unique order-16 component has exactly two internal ambient neighbors at
every vertex, while every order-8 component has exactly one. -/
theorem orderSixtyFour_seven_defect_components_local_degrees
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
      (∀ x ∈ c.supp,
        ((G.neighborFinset x).filter (fun y =>
          (secondOrderDefectGraph G).connectedComponentMk y = c)).card = 2) ∧
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ x ∈ e.supp,
          ((G.neighborFinset x).filter (fun y =>
            (secondOrderDefectGraph G).connectedComponentMk y = e)).card = 1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hothers⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_, ?_⟩
  · intro x _hx
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover c x
    change 8 * ((G.neighborFinset x).filter (fun y =>
      (secondOrderDefectGraph G).connectedComponentMk y = c)).card =
        c.supp.ncard at h
    rw [hc16] at h
    omega
  · intro e hec
    have he8 := hothers e hec
    refine ⟨he8, ?_⟩
    intro x _hx
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover e x
    change 8 * ((G.neighborFinset x).filter (fun y =>
      (secondOrderDefectGraph G).connectedComponentMk y = e)).card =
        e.supp.ncard at h
    rw [he8] at h
    omega

/-- Stronger equitable form: every ambient vertex—not only vertices of the
target component—has two neighbors in the order-16 block and one neighbor
in each order-8 block. -/
theorem orderSixtyFour_seven_defect_components_global_block_degrees
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
      (∀ x, (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2) ∧
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ x, (componentNeighborFinset G
          (secondOrderDefectGraph G) e x).card = 1 := by
  classical
  obtain ⟨c, hc16, hothers⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_, ?_⟩
  · intro x
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover c x
    rw [hc16] at h
    omega
  · intro e hec
    have he8 := hothers e hec
    refine ⟨he8, ?_⟩
    intro x
    have h := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover e x
    rw [he8] at h
    omega

end

end Erdos85
