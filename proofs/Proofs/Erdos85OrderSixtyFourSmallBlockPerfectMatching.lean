import Proofs.Erdos85OrderSixtyFourSixteenPairComplement

/-! # The six small blocks give perfect matchings on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Each order-eight defect block labels eight pairs on H16 in which every
H16 vertex occurs exactly once.  This is the incidence formulation of a
perfect matching, avoiding any choice of an explicit edge type. -/
theorem orderSixtyFour_seven_defect_components_smallBlock_pair_unique_incidence
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
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ u : c.supp, ∃! x : e.supp,
          u.1 ∈ componentNeighborFinset G
            (secondOrderDefectGraph G) c x.1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _htwo, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hone⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro u
  let S := componentNeighborFinset G D e u.1
  have hScard : S.card = 1 := hone u.1
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hScard
  have hxS : x ∈ S := by rw [hx]; simp
  have hxcomp : x ∈ e.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (Finset.mem_filter.mp hxS).2
  let xs : e.supp := ⟨x, hxcomp⟩
  refine ⟨xs, ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨?_, (ConnectedComponent.mem_supp_iff c u.1).mp u.2⟩
    have hux : G.Adj u.1 x :=
      (G.mem_neighborFinset u.1 x).mp (Finset.mem_filter.mp hxS).1
    exact (G.mem_neighborFinset x u.1).mpr hux.symm
  · intro y hy
    apply Subtype.ext
    have hyAdj : G.Adj u.1 y.1 := by
      have hy' := (Finset.mem_filter.mp hy).1
      exact ((G.mem_neighborFinset y.1 u.1).mp hy').symm
    have hyS : y.1 ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset u.1 y.1).mpr hyAdj, ?_⟩
      exact (ConnectedComponent.mem_supp_iff e y.1).mp y.2
    rw [hx] at hyS
    simpa [xs] using hyS

end

end Erdos85
