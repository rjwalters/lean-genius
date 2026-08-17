import Proofs.Erdos85OrderSixtyFourSevenComponentPairPacking

/-! # Global pair injection into the order-sixteen block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-component branch every ambient vertex has exactly two
neighbors in the distinguished order-sixteen block, and these unordered
pairs are distinct for all 64 vertices.  Equality for two different source
vertices would give them two common neighbors and hence a four-cycle. -/
theorem orderSixtyFour_seven_defect_components_sixteen_pair_injective
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
      Function.Injective
        (componentNeighborFinset G (secondOrderDefectGraph G) c) := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro y z heq
  by_contra hyz
  let Sy := componentNeighborFinset G D c y
  have hSycard : Sy.card = 2 := htwo y
  have hsub : Sy ⊆ G.neighborFinset y ∩ G.neighborFinset z := by
    intro w hw
    have hwy : G.Adj y w :=
      (G.mem_neighborFinset y w).mp ((Finset.mem_filter.mp hw).1)
    have hwzS : w ∈ componentNeighborFinset G D c z := by
      rw [← heq]
      exact hw
    have hwz : G.Adj z w :=
      (G.mem_neighborFinset z w).mp ((Finset.mem_filter.mp hwzS).1)
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset y w).mpr hwy,
        (G.mem_neighborFinset z w).mpr hwz⟩
  have hle : Sy.card ≤
      (G.neighborFinset y ∩ G.neighborFinset z).card :=
    Finset.card_le_card hsub
  have hone := common_le_one_of_not_containsC4 hfree y z hyz
  omega

/-- Consequently the 48 vertices outside the distinguished block select
exactly 48 distinct two-element neighbor pairs inside it. -/
theorem orderSixtyFour_seven_defect_components_outside_pair_image_card
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
      ((Finset.univ.filter (fun x : Fin 64 ↦ x ∉ c.supp)).image
        (componentNeighborFinset G (secondOrderDefectGraph G) c)).card = 48 := by
  classical
  obtain ⟨c, hc16, hinj⟩ :=
    orderSixtyFour_seven_defect_components_sixteen_pair_injective
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  rw [Finset.card_image_of_injective _ hinj]
  have hfilter :
      (Finset.univ.filter (fun x : Fin 64 ↦ x ∉ c.supp)) =
        Finset.univ \ c.supp.toFinset := by
    ext x
    simp
  rw [hfilter, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, Fintype.card_fin,
    ← Set.ncard_eq_toFinset_card', hc16]

end

end Erdos85
