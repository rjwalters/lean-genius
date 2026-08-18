import Proofs.Erdos85OrderSixtyFourResidualInjective

/-! # Pair packing on the order-16 block in the seven-component branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Vertices belonging to two different order-8 defect blocks select
different two-element neighbor sets in the unique order-16 block.  Equality
would give the two vertices two common neighbors and hence a four-cycle. -/
theorem orderSixtyFour_seven_defect_components_cross_pair_injective
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
      ∀ e, e ≠ c → ∀ f, f ≠ c → e ≠ f →
        ∀ y z : Fin 64,
          (secondOrderDefectGraph G).connectedComponentMk y = e →
          (secondOrderDefectGraph G).connectedComponentMk z = f →
          componentNeighborFinset G (secondOrderDefectGraph G) c y ≠
            componentNeighborFinset G (secondOrderDefectGraph G) c z := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e _hec f _hfc hef y z hy hz heq
  have hyz : y ≠ z := by
    intro hyz
    subst z
    rw [hy] at hz
    exact hef hz
  let Sy := componentNeighborFinset G D c y
  let Sz := componentNeighborFinset G D c z
  have hSycard : Sy.card = 2 := htwo y
  have hsub : Sy ⊆ G.neighborFinset y ∩ G.neighborFinset z := by
    intro w hw
    have hwy : G.Adj y w := by
      exact (G.mem_neighborFinset y w).mp
        ((Finset.mem_filter.mp hw).1)
    have hwzS : w ∈ Sz := by
      dsimp only [Sz, D]
      rw [← heq]
      simpa only [Sy, D] using hw
    have hwz : G.Adj z w := by
      exact (G.mem_neighborFinset z w).mp
        ((Finset.mem_filter.mp hwzS).1)
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset y w).mpr hwy,
        (G.mem_neighborFinset z w).mpr hwz⟩
  have hle : Sy.card ≤
      (G.neighborFinset y ∩ G.neighborFinset z).card :=
    Finset.card_le_card hsub
  have hone := common_le_one_of_not_containsC4 hfree y z hyz
  omega

end

end Erdos85
