import Proofs.Erdos85BinarySquareCanonicalForkCoincidentCenterExhaustion
import Proofs.Erdos85OrderSixtyFourDistinctCentersSaturateRoutingRow

/-! # Two-branch canonical terminal for an owner fork -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- A forced owner fork in the exact-two-lift regime has only two surviving
canonical ambient configurations. -/
theorem orderSixtyFour_ownerFork_coincidentSelectorExhaustion_or_routingRowSaturation
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {d e f₁ f₂ b c :
      (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hz : z₁.1 ≠ z₂.1)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hcx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1)
    (hcx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1)
    (hbcard : (componentNeighborFinset G (secondOrderDefectGraph G) b y.1).card = 2)
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
    (uc₁ = uc₂ ∧ ub₁ ≠ ub₂ ∧
      componentNeighborFinset G (secondOrderDefectGraph G) b y.1 = {ub₁, ub₂}) ∨
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
  by_cases hsame : uc₁ = uc₂
  · left
    have hexhaust := ownerFork_coincident_cCenters_canonical_bSelector_exhaustion
      G hfree hde hef₁ hef₂ hdf₁ hdf₂ hbc x y z₁ z₂ hz
        hby₁ hby₂ hcx₁ hcx₂ (congrArg Subtype.val hsame) hbcard
    change ub₁ ≠ ub₂ ∧
      componentNeighborFinset G (secondOrderDefectGraph G) b y.1 = {ub₁, ub₂}
      at hexhaust
    exact ⟨hsame, hexhaust⟩
  · right
    apply orderSixtyFour_twoClosingRoutes_distinctCenters_union_eq_row
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ x z₁ z₂
        hdirect₁ hdirect₂
    · intro h
      exact hsame (Subtype.ext h)
    · exact hallTwo

end

end Erdos85
