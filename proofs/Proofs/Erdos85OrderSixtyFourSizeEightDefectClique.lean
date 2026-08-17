import Proofs.Erdos85OrderSixtyFourResidualDeterminantSquare

/-! # Size-eight components of the order-64 defect are cliques -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem card_filter_component''
    (D : SimpleGraph (Fin 64)) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    ((Finset.univ : Finset (Fin 64)).filter
      (fun x => D.connectedComponentMk x = c)).card = c.supp.ncard := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- A seven-regular connected component on eight vertices is complete. -/
theorem sevenRegular_component_order_eight_adj
    (D : SimpleGraph (Fin 64)) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    (hreg : ∀ x : Fin 64, D.degree x = 7)
    (c : D.ConnectedComponent) (hc8 : c.supp.ncard = 8)
    {x y : Fin 64}
    (hx : D.connectedComponentMk x = c)
    (hy : D.connectedComponentMk y = c) (hxy : x ≠ y) :
    D.Adj x y := by
  classical
  have hxmem : x ∈ (Finset.univ : Finset (Fin 64)).filter
      (fun z => D.connectedComponentMk z = c) := by simp [hx]
  have hneighbors : D.neighborFinset x =
      ((Finset.univ : Finset (Fin 64)).filter
        (fun z => D.connectedComponentMk z = c)).erase x := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have hxz : D.Adj x z := (D.mem_neighborFinset x z).mp hz
      have hcomp : D.connectedComponentMk z = c :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨(D.ne_of_adj hxz).symm, hcomp⟩
    · rw [D.card_neighborFinset_eq_degree, hreg]
      rw [Finset.card_erase_of_mem hxmem,
        card_filter_component'', hc8]
  have hymem : y ∈ ((Finset.univ : Finset (Fin 64)).filter
      (fun z => D.connectedComponentMk z = c)).erase x := by
    simp [hy, hxy.symm]
  rw [← hneighbors] at hymem
  exact (D.mem_neighborFinset x y).mp hymem

/-- Graph-facing specialization: every order-eight component of the
order-64 second-order defect is a `K₈`. -/
theorem orderSixtyFour_sizeEight_defect_component_adj
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc8 : c.supp.ncard = 8)
    {x y : Fin 64}
    (hx : (secondOrderDefectGraph G).connectedComponentMk x = c)
    (hy : (secondOrderDefectGraph G).connectedComponentMk y = c)
    (hxy : x ≠ y) :
    (secondOrderDefectGraph G).Adj x y := by
  apply sevenRegular_component_order_eight_adj
    (secondOrderDefectGraph G)
    (orderSixtyFour_regular_defect_kernel G hfree hmin hcover).2.2.1
    c hc8 hx hy hxy

end

end Erdos85
