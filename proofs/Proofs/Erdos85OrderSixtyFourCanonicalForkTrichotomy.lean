import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters
import Proofs.Erdos85OrderSixtyFourRoutingCenterDichotomy

/-! # Canonical center trichotomy for a forced owner fork -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- Combining canonical fork-center separation with exact routing lifts leaves
three explicit ambient configurations. -/
theorem orderSixtyFour_ownerFork_canonicalCenter_trichotomy
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {d e f₁ f₂ a b c :
      (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hz : z₁.1 ≠ z₂.1)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hcx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1)
    (hcx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1)
    (hallTwo : ∀ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) :
    let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
    let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
    let uc₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
      apply (ConnectedComponent.mem_supp_iff c _).mpr
      calc
        (secondOrderDefectGraph G).connectedComponentMk
            (crossCommonNeighbor G hfree hdf₁ x z₁) =
            crossIntermediateComponent G hfree hdf₁ x z₁ :=
          (ConnectedComponent.mem_supp_iff _ _).mp
            (crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁)
        _ = c := by
          rw [crossIntermediateComponent_reverse G hfree hdf₁ x z₁]
          exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
            G hfree hdf₁.symm z₁ x c hcx₁⟩
    let uc₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
      apply (ConnectedComponent.mem_supp_iff c _).mpr
      calc
        (secondOrderDefectGraph G).connectedComponentMk
            (crossCommonNeighbor G hfree hdf₂ x z₂) =
            crossIntermediateComponent G hfree hdf₂ x z₂ :=
          (ConnectedComponent.mem_supp_iff _ _).mp
            (crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂)
        _ = c := by
          rw [crossIntermediateComponent_reverse G hfree hdf₂ x z₂]
          exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
            G hfree hdf₂.symm z₂ x c hcx₂⟩
    let R := (Finset.univ : Finset e.supp).filter fun w =>
      c = crossIntermediateComponent G hfree hde x w
    (ub₁ ≠ ub₂ ∧ uc₁ = uc₂) ∨
      (restrictedComponentOwnerGraph G c e).Adj uc₁ uc₂ ∨
      componentCrossNeighborFinset G e uc₁ ∪
        componentCrossNeighborFinset G e uc₂ = R := by
  classical
  let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
  let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
  have hdirect₁ : c = crossIntermediateComponent G hfree hdf₁ x z₁ := by
    rw [crossIntermediateComponent_reverse G hfree hdf₁ x z₁]
    exact (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₁.symm z₁ x c hcx₁).symm
  have hdirect₂ : c = crossIntermediateComponent G hfree hdf₂ x z₂ := by
    rw [crossIntermediateComponent_reverse G hfree hdf₂ x z₂]
    exact (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₂.symm z₂ x c hcx₂).symm
  let uc₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
    rw [hdirect₁]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁⟩
  let uc₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
    rw [hdirect₂]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂⟩
  let R := (Finset.univ : Finset e.supp).filter fun w =>
    c = crossIntermediateComponent G hfree hde x w
  have hsep := ownerFork_canonicalCenter_separation G hfree hde hef₁ hef₂
    hdf₁ hdf₂ hbc x y z₁ z₂ hz hby₁ hby₂ hcx₁ hcx₂
  change ub₁ ≠ ub₂ ∨ uc₁.1 ≠ uc₂.1 at hsep
  have hcenters :=
    orderSixtyFour_twoClosingRoutes_center_eq_or_ownerAdj_or_union_eq_row
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ x z₁ z₂
        hdirect₁ hdirect₂ hallTwo
  change uc₁ = uc₂ ∨ (restrictedComponentOwnerGraph G c e).Adj uc₁ uc₂ ∨
    componentCrossNeighborFinset G e uc₁ ∪
      componentCrossNeighborFinset G e uc₂ = R at hcenters
  rcases hcenters with hsame | hadj | hsaturate
  · left
    refine ⟨?_, hsame⟩
    rcases hsep with hub | huc
    · exact hub
    · exact False.elim (huc (congrArg Subtype.val hsame))
  · exact Or.inr (Or.inl hadj)
  · exact Or.inr (Or.inr hsaturate)

end

end Erdos85
