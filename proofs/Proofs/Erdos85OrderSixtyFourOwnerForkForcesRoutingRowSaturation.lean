import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters
import Proofs.Erdos85OrderSixtyFourDistinctCentersSaturateRoutingRow

/-! # Every exact owner fork forces routing-row saturation -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- Whichever side supplies the separated canonical centers, its two ambient
star rows disjointly saturate the corresponding four-point routing row. -/
theorem orderSixtyFour_ownerFork_forces_routingRowSaturation
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
    (hallTwo : ∀ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) :
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
    let ub₁ : b.supp := ⟨crossCommonNeighbor G hfree hef₁ y z₁, by
      apply (ConnectedComponent.mem_supp_iff b _).mpr
      calc
        (secondOrderDefectGraph G).connectedComponentMk
            (crossCommonNeighbor G hfree hef₁ y z₁) =
            crossIntermediateComponent G hfree hef₁ y z₁ :=
          (ConnectedComponent.mem_supp_iff _ _).mp
            (crossCommonNeighbor_mem_intermediate G hfree hef₁ y z₁)
        _ = b := crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
          G hfree hef₁ y z₁ b hby₁⟩
    let ub₂ : b.supp := ⟨crossCommonNeighbor G hfree hef₂ y z₂, by
      apply (ConnectedComponent.mem_supp_iff b _).mpr
      calc
        (secondOrderDefectGraph G).connectedComponentMk
            (crossCommonNeighbor G hfree hef₂ y z₂) =
            crossIntermediateComponent G hfree hef₂ y z₂ :=
          (ConnectedComponent.mem_supp_iff _ _).mp
            (crossCommonNeighbor_mem_intermediate G hfree hef₂ y z₂)
        _ = b := crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
          G hfree hef₂ y z₂ b hby₂⟩
    let Rc := (Finset.univ : Finset e.supp).filter fun w =>
      c = crossIntermediateComponent G hfree hde x w
    let Rb := (Finset.univ : Finset d.supp).filter fun w =>
      b = crossIntermediateComponent G hfree hde.symm y w
    (componentCrossNeighborFinset G e uc₁ ∪
      componentCrossNeighborFinset G e uc₂ = Rc) ∨
    (componentCrossNeighborFinset G d ub₁ ∪
      componentCrossNeighborFinset G d ub₂ = Rb) := by
  classical
  have hcdirect₁ : c = crossIntermediateComponent G hfree hdf₁ x z₁ := by
    rw [crossIntermediateComponent_reverse G hfree hdf₁ x z₁]
    exact (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₁.symm z₁ x c hcx₁).symm
  have hcdirect₂ : c = crossIntermediateComponent G hfree hdf₂ x z₂ := by
    rw [crossIntermediateComponent_reverse G hfree hdf₂ x z₂]
    exact (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₂.symm z₂ x c hcx₂).symm
  have hbdirect₁ : b = crossIntermediateComponent G hfree hef₁ y z₁ :=
    (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₁ y z₁ b hby₁).symm
  have hbdirect₂ : b = crossIntermediateComponent G hfree hef₂ y z₂ :=
    (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₂ y z₂ b hby₂).symm
  let uc₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
    rw [hcdirect₁]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁⟩
  let uc₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
    rw [hcdirect₂]
    exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂⟩
  let ub₁ : b.supp := ⟨crossCommonNeighbor G hfree hef₁ y z₁, by
    rw [hbdirect₁]
    exact crossCommonNeighbor_mem_intermediate G hfree hef₁ y z₁⟩
  let ub₂ : b.supp := ⟨crossCommonNeighbor G hfree hef₂ y z₂, by
    rw [hbdirect₂]
    exact crossCommonNeighbor_mem_intermediate G hfree hef₂ y z₂⟩
  let Rc := (Finset.univ : Finset e.supp).filter fun w =>
    c = crossIntermediateComponent G hfree hde x w
  let Rb := (Finset.univ : Finset d.supp).filter fun w =>
    b = crossIntermediateComponent G hfree hde.symm y w
  by_cases hcsep : uc₁ ≠ uc₂
  · left
    apply orderSixtyFour_twoClosingRoutes_distinctCenters_union_eq_row
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ x z₁ z₂
        hcdirect₁ hcdirect₂
    · exact fun h => hcsep (Subtype.ext h)
    · exact hallTwo
  · right
    have hcanonical := ownerFork_canonicalCenter_separation G hfree hde
      hef₁ hef₂ hdf₁ hdf₂ hbc x y z₁ z₂ hz hby₁ hby₂ hcx₁ hcx₂
    change ub₁.1 ≠ ub₂.1 ∨ uc₁.1 ≠ uc₂.1 at hcanonical
    have hbsep : ub₁ ≠ ub₂ := by
      have huceq : uc₁ = uc₂ := not_ne_iff.mp hcsep
      have hucvaleq : uc₁.1 = uc₂.1 := congrArg Subtype.val huceq
      have hbval := hcanonical.resolve_right (fun h => h hucvaleq)
      intro h
      exact hbval (congrArg Subtype.val h)
    apply orderSixtyFour_twoClosingRoutes_distinctCenters_union_eq_row
      G hfree hreg hcount hde.symm hef₁ hef₂ hdf₁ hdf₂ y z₁ z₂
        hbdirect₁ hbdirect₂
    · exact fun h => hbsep (Subtype.ext h)
    · exact hallTwo

end

end Erdos85
