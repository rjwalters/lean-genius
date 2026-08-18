import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowFork
import Proofs.Erdos85OrderSixtyFourRoutingForkSaturation

/-! # The no-rainbow branch forces a saturated routing row -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two ambient star rows exhaust a four-point routing-color row. -/
def routingRowSaturatedAt
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    {source middle : (secondOrderDefectGraph G).ConnectedComponent}
    (hsm : source ≠ middle)
    (route : (secondOrderDefectGraph G).ConnectedComponent)
    (x : source.supp) : Prop :=
  ∃ u₁ u₂ : route.supp,
    componentCrossNeighborFinset G middle u₁ ∪
      componentCrossNeighborFinset G middle u₂ =
        ((Finset.univ : Finset middle.supp).filter fun w =>
          route = crossIntermediateComponent G hfree hsm x w)

set_option maxRecDepth 10000 in
/-- Under global absence of owner rainbows, every chosen root and distinct
ordered color triple produces some saturated routing row. -/
theorem orderSixtyFour_regular_fourComponents_noRainbow_exists_routingRowSaturatedAt
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (hno : ¬ ∃ c d e f : (secondOrderDefectGraph G).ConnectedComponent,
      c ≠ e ∧ e ≠ f ∧ c ≠ f ∧ routingOwnerRainbow G d e f c)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x : Fin 64) :
    ∃ (source middle route :
        (secondOrderDefectGraph G).ConnectedComponent)
      (hsm : source ≠ middle) (root : source.supp),
      routingRowSaturatedAt G hfree hsm route root := by
  classical
  let D := secondOrderDefectGraph G
  have hlocal : ¬ ∃ d : D.ConnectedComponent,
      routingOwnerRainbow G d a b c := by
    rintro ⟨d, hd⟩
    exact hno ⟨c, d, a, b, hac.symm, hab, hbc.symm, hd⟩
  obtain ⟨e, y, z₁, z₂, hene, hycomp, hz, hz₁e, hz₁x,
      hz₂e, hz₂x, _haxy, hby₁, hcz₁, hby₂, hcz₂⟩ :=
    orderSixtyFour_regular_fourComponents_noRainbow_exists_ownerFork
      G hfree hreg hcount a b c hab hac hbc hlocal x
  have hallTwo :=
    (orderSixtyFour_regular_fourComponents_rainbow_or_all_direct_two_lifts
      G hfree hreg hcount).resolve_left hno
  let d := D.connectedComponentMk x
  let f₁ := D.connectedComponentMk z₁
  let f₂ := D.connectedComponentMk z₂
  have hde : d ≠ e := hene.symm
  have hef₁ : e ≠ f₁ := hz₁e.symm
  have hef₂ : e ≠ f₂ := hz₂e.symm
  have hdf₁ : d ≠ f₁ := hz₁x.symm
  have hdf₂ : d ≠ f₂ := hz₂x.symm
  let xs : d.supp := ⟨x, ConnectedComponent.connectedComponentMk_mem⟩
  let ys : e.supp := ⟨y, (ConnectedComponent.mem_supp_iff e y).mpr hycomp⟩
  let z₁s : f₁.supp := ⟨z₁, ConnectedComponent.connectedComponentMk_mem⟩
  let z₂s : f₂.supp := ⟨z₂, ConnectedComponent.connectedComponentMk_mem⟩
  have hb₁ : b = crossIntermediateComponent G hfree hef₁ ys z₁s := by
    symm
    exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₁ ys z₁s b hby₁
  have hb₂ : b = crossIntermediateComponent G hfree hef₂ ys z₂s := by
    symm
    exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₂ ys z₂s b hby₂
  have hc₁ : c = crossIntermediateComponent G hfree hdf₁ xs z₁s := by
    rw [crossIntermediateComponent_reverse G hfree hdf₁ xs z₁s]
    exact (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₁.symm z₁s xs c hcz₁).symm
  have hc₂ : c = crossIntermediateComponent G hfree hdf₂ xs z₂s := by
    rw [crossIntermediateComponent_reverse G hfree hdf₂ xs z₂s]
    exact (crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₂.symm z₂s xs c hcz₂).symm
  have hsaturation :=
    orderSixtyFour_routingFork_centerSeparation_forces_saturation
      G hfree hreg hcount hde hdf₁ hdf₂ hef₁ hef₂ xs ys z₁s z₂s
        hb₁ hb₂ hc₁ hc₂ hz hbc hallTwo
  rcases hsaturation with hbSat | hcSat
  · refine ⟨e, d, b, hde.symm, ys, ?_⟩
    let ub₁ : b.supp := ⟨crossCommonNeighbor G hfree hef₁ ys z₁s, by
      rw [hb₁]
      exact crossCommonNeighbor_mem_intermediate G hfree hef₁ ys z₁s⟩
    let ub₂ : b.supp := ⟨crossCommonNeighbor G hfree hef₂ ys z₂s, by
      rw [hb₂]
      exact crossCommonNeighbor_mem_intermediate G hfree hef₂ ys z₂s⟩
    exact ⟨ub₁, ub₂, hbSat⟩
  · refine ⟨d, e, c, hde, xs, ?_⟩
    let uc₁ : c.supp := ⟨crossCommonNeighbor G hfree hdf₁ xs z₁s, by
      rw [hc₁]
      exact crossCommonNeighbor_mem_intermediate G hfree hdf₁ xs z₁s⟩
    let uc₂ : c.supp := ⟨crossCommonNeighbor G hfree hdf₂ xs z₂s, by
      rw [hc₂]
      exact crossCommonNeighbor_mem_intermediate G hfree hdf₂ xs z₂s⟩
    exact ⟨uc₁, uc₂, hcSat⟩

end

end Erdos85
