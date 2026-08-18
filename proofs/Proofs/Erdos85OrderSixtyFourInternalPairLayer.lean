import Proofs.Erdos85OrderSixtyFourSmallBlockPerfectMatching

/-! # The internal distance-two pair layer on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For a vertex of H16, its selected pair is exactly its two neighbors in
the ambient graph induced on H16.  These sixteen internal pairs are all
distinct. -/
theorem orderSixtyFour_seven_defect_components_internal_pair_layer
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
      (∀ x : c.supp,
        componentNeighborFinset G (secondOrderDefectGraph G) c x.1 =
          ((G.induce c.supp).neighborFinset x).map
            (.subtype (fun y ↦ y ∈ c.supp))) ∧
      Function.Injective (fun x : c.supp ↦
        componentNeighborFinset G (secondOrderDefectGraph G) c x.1) ∧
      ((Finset.univ : Finset c.supp).image (fun x : c.supp ↦
        componentNeighborFinset G (secondOrderDefectGraph G) c x.1)).card = 16 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hinj⟩ :=
    orderSixtyFour_seven_defect_components_sixteen_pair_injective
      G hfree hmin hcover hcount
  have heq (x : c.supp) :
      componentNeighborFinset G D c x.1 =
        ((G.induce c.supp).neighborFinset x).map
          (.subtype (fun y ↦ y ∈ c.supp)) := by
    rw [G.map_neighborFinset_induce x]
    ext y
    simp [D, componentNeighborFinset,
      ConnectedComponent.mem_supp_iff]
  have hinjSub : Function.Injective (fun x : c.supp ↦
      componentNeighborFinset G D c x.1) := by
    intro x y hxy
    apply Subtype.ext
    exact hinj hxy
  refine ⟨c, hc16, heq, hinjSub, ?_⟩
  rw [Finset.card_image_of_injective _ hinjSub,
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq, hc16]

end

end Erdos85
