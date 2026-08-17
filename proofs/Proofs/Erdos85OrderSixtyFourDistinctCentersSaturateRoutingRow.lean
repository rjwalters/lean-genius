import Proofs.Erdos85OrderSixtyFourRoutingCenterDichotomy
import Proofs.Erdos85BinarySquareSeparatedCentersDisjointSelectors

/-! # Distinct direct centers force routing-row saturation -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- In the exact-two-lift branch, two distinct direct common-neighbor centers
cannot take the owner-adjacent/shared-hub alternative: they already share the
root outside the middle component.  Their two lift rows therefore saturate
the four-point routing row. -/
theorem orderSixtyFour_twoClosingRoutes_distinctCenters_union_eq_row
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {d e f₁ f₂ c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂)
    (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (x : d.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hdirect₁ : c = crossIntermediateComponent G hfree hdf₁ x z₁)
    (hdirect₂ : c = crossIntermediateComponent G hfree hdf₂ x z₂)
    (hcenters : crossCommonNeighbor G hfree hdf₁ x z₁ ≠
      crossCommonNeighbor G hfree hdf₂ x z₂)
    (hallTwo : ∀ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) :
    let u₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
      rw [hdirect₁]
      exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁⟩
    let u₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
      rw [hdirect₂]
      exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂⟩
    let R := (Finset.univ : Finset e.supp).filter fun y =>
      c = crossIntermediateComponent G hfree hde x y
    componentCrossNeighborFinset G e u₁ ∪
      componentCrossNeighborFinset G e u₂ = R := by
  classical
  let u₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
    rw [hdirect₁]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁⟩
  let u₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
    rw [hdirect₂]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂⟩
  let R := (Finset.univ : Finset e.supp).filter fun y =>
    c = crossIntermediateComponent G hfree hde x y
  have hcases :=
    orderSixtyFour_twoClosingRoutes_center_eq_or_ownerAdj_or_union_eq_row
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ x z₁ z₂
        hdirect₁ hdirect₂ hallTwo
  change u₁ = u₂ ∨ (restrictedComponentOwnerGraph G c e).Adj u₁ u₂ ∨
    componentCrossNeighborFinset G e u₁ ∪
      componentCrossNeighborFinset G e u₂ = R at hcases
  rcases hcases with heq | hadj | hsaturate
  · exact False.elim (hcenters (congrArg Subtype.val heq))
  · have hadj' :=
      (restrictedOwner_adj_iff_crossNeighbor_inter_nonempty G c e u₁ u₂).mp hadj
    have hdisjoint :=
      componentCrossNeighborFinset_disjoint_of_distinct_sharedNeighbor_outside
        G hfree u₁ u₂
          (fun h => hcenters (congrArg Subtype.val h))
          (crossCommonNeighbor_spec G hfree hdf₁ x z₁).1.symm
          (crossCommonNeighbor_spec G hfree hdf₂ x z₂).1.symm hde
    have hempty : componentCrossNeighborFinset G e u₁ ∩
        componentCrossNeighborFinset G e u₂ = ∅ := by
      exact Finset.disjoint_iff_inter_eq_empty.mp hdisjoint
    exact False.elim (by simpa [hempty] using hadj'.2)
  · exact hsaturate

end

end Erdos85
