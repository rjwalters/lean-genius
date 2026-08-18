import Proofs.Erdos85OrderSixtyFourDistinctCentersSaturateRoutingRow

/-! # One side of every separated routing fork saturates -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000 in
/-- For a two-closing routing fork, separation of either pair of direct
centers forces the corresponding two exact-lift selectors to saturate their
four-point routing row. -/
theorem orderSixtyFour_routingFork_centerSeparation_forces_saturation
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {d e f₁ f₂ b c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂)
    (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hb₁ : b = crossIntermediateComponent G hfree hef₁ y z₁)
    (hb₂ : b = crossIntermediateComponent G hfree hef₂ y z₂)
    (hc₁ : c = crossIntermediateComponent G hfree hdf₁ x z₁)
    (hc₂ : c = crossIntermediateComponent G hfree hdf₂ x z₂)
    (hz : z₁.1 ≠ z₂.1) (hbc : b ≠ c)
    (hallTwo : ∀ c d e f :
      (secondOrderDefectGraph G).ConnectedComponent,
      ∀ (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f),
      ∀ (x : c.supp) (w : f.supp),
        d = crossIntermediateComponent G hfree hcf x w →
        ((Finset.univ : Finset e.supp).filter fun z =>
          d = crossIntermediateComponent G hfree hce x z ∧
            d = crossIntermediateComponent G hfree hef z w).card = 2) :
    (let ub₁ : b.supp := ⟨crossCommonNeighbor G hfree hef₁ y z₁, by
        rw [hb₁]
        exact crossCommonNeighbor_mem_intermediate G hfree hef₁ y z₁⟩
      let ub₂ : b.supp := ⟨crossCommonNeighbor G hfree hef₂ y z₂, by
        rw [hb₂]
        exact crossCommonNeighbor_mem_intermediate G hfree hef₂ y z₂⟩
      let Rb := (Finset.univ : Finset d.supp).filter fun w =>
        b = crossIntermediateComponent G hfree hde.symm y w
      componentCrossNeighborFinset G d ub₁ ∪
        componentCrossNeighborFinset G d ub₂ = Rb) ∨
    (let uc₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ x z₁, by
        rw [hc₁]
        exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁⟩
      let uc₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ x z₂, by
        rw [hc₂]
        exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂⟩
      let Rc := (Finset.univ : Finset e.supp).filter fun w =>
        c = crossIntermediateComponent G hfree hde x w
      componentCrossNeighborFinset G e uc₁ ∪
        componentCrossNeighborFinset G e uc₂ = Rc) := by
  have hsep :
      crossCommonNeighbor G hfree hef₁ y z₁ ≠
          crossCommonNeighbor G hfree hef₂ y z₂ ∨
        crossCommonNeighbor G hfree hdf₁ x z₁ ≠
          crossCommonNeighbor G hfree hdf₂ x z₂ := by
    by_contra hs
    push Not at hs
    let ub := crossCommonNeighbor G hfree hef₁ y z₁
    let uc := crossCommonNeighbor G hfree hdf₁ x z₁
    have hzb₁ : G.Adj z₁.1 ub :=
      (crossCommonNeighbor_spec G hfree hef₁ y z₁).2
    have hzb₂ : G.Adj z₂.1 ub := by
      dsimp [ub]
      rw [hs.1]
      exact (crossCommonNeighbor_spec G hfree hef₂ y z₂).2
    have hzc₁ : G.Adj z₁.1 uc :=
      (crossCommonNeighbor_spec G hfree hdf₁ x z₁).2
    have hzc₂ : G.Adj z₂.1 uc := by
      dsimp [uc]
      rw [hs.2]
      exact (crossCommonNeighbor_spec G hfree hdf₂ x z₂).2
    have hubcomp : (secondOrderDefectGraph G).connectedComponentMk ub = b := by
      have hmem := (ConnectedComponent.mem_supp_iff _ _).mp
        (crossCommonNeighbor_mem_intermediate G hfree hef₁ y z₁)
      dsimp [ub]
      exact hmem.trans hb₁.symm
    have huccomp : (secondOrderDefectGraph G).connectedComponentMk uc = c := by
      have hmem := (ConnectedComponent.mem_supp_iff _ _).mp
        (crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁)
      dsimp [uc]
      exact hmem.trans hc₁.symm
    have hubc : ub ≠ uc := by
      intro h
      apply hbc
      exact hubcomp.symm.trans ((congrArg
        (secondOrderDefectGraph G).connectedComponentMk h).trans huccomp)
    have hubMem : ub ∈ G.neighborFinset z₁.1 ∩ G.neighborFinset z₂.1 := by
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z₁.1 ub).mpr hzb₁,
          (G.mem_neighborFinset z₂.1 ub).mpr hzb₂⟩
    have hucMem : uc ∈ G.neighborFinset z₁.1 ∩ G.neighborFinset z₂.1 := by
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z₁.1 uc).mpr hzc₁,
          (G.mem_neighborFinset z₂.1 uc).mpr hzc₂⟩
    have hle := card_inter_neighborFinset_le_one hfree hz
    exact hubc (Finset.card_le_one.mp hle ub hubMem uc hucMem)
  rcases hsep with hbsep | hcsep
  · left
    exact orderSixtyFour_twoClosingRoutes_distinctCenters_union_eq_row
      G hfree hreg hcount hde.symm hef₁ hef₂ hdf₁ hdf₂ y z₁ z₂
        hb₁ hb₂ hbsep hallTwo
  · right
    exact orderSixtyFour_twoClosingRoutes_distinctCenters_union_eq_row
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ x z₁ z₂
        hc₁ hc₂ hcsep hallTwo

end

end Erdos85
