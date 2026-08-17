import Proofs.Erdos85CrossDefectComponentCommonNeighbor
import Proofs.Erdos85OrderSixtyFourSevenComponentLocal

/-! # External completion of cross-block label pairs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-component branch, a pair of labels from distinct small
blocks has a unique common neighbor.  If it has no common neighbor in H16,
that completion lies in one of the six order-eight defect blocks. -/
theorem orderSixtyFour_seven_defect_components_external_completion
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
        ∀ f, f ≠ c → f.supp.ncard = 8 ∧
          ∀ (_hef : e ≠ f), ∀ x : e.supp, ∀ y : f.supp,
            (¬ ∃ u : c.supp, G.Adj x.1 u.1 ∧ G.Adj y.1 u.1) →
            ∃! z : Fin 64,
              G.Adj x.1 z ∧ G.Adj y.1 z ∧
              (secondOrderDefectGraph G).connectedComponentMk z ≠ c ∧
              ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard = 8 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _htwo, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, _⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, _⟩ := hsmall f hfc
  refine ⟨hf8, ?_⟩
  intro hef x y hnoH
  obtain ⟨z, hz, huniq⟩ :=
    existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hef x y
  have hzout : D.connectedComponentMk z ≠ c := by
    intro hzc
    apply hnoH
    have hzmem : z ∈ c.supp :=
      (ConnectedComponent.mem_supp_iff c z).mpr hzc
    exact ⟨⟨z, hzmem⟩, hz⟩
  have hz8 : (D.connectedComponentMk z).supp.ncard = 8 :=
    (hsmall (D.connectedComponentMk z) hzout).1
  refine ⟨z, ⟨hz.1, hz.2, hzout, hz8⟩, ?_⟩
  intro w hw
  exact huniq w ⟨hw.1, hw.2.1⟩

end

end Erdos85
