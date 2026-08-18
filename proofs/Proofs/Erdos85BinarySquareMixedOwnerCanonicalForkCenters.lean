import Proofs.Erdos85BinarySquareMixedOwnerNoRainbowFork

/-! # Canonical ambient centers of a mixed-owner fork -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The four canonical common-neighbor centers of an owner fork cannot
coincide in pairs on both sides.  No separation between the two fork roots is
needed; only each root must lie outside the closing components. -/
theorem ownerFork_canonicalCenter_separation_without_root_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f₁ f₂ b c :
      (secondOrderDefectGraph G).ConnectedComponent}
    (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hz : z₁.1 ≠ z₂.1)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hcx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1)
    (hcx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1) :
    let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
    let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
    let uc₁ := crossCommonNeighbor G hfree hdf₁ x z₁
    let uc₂ := crossCommonNeighbor G hfree hdf₂ x z₂
    ub₁ ≠ ub₂ ∨ uc₁ ≠ uc₂ := by
  classical
  let D := secondOrderDefectGraph G
  let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
  let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
  let uc₁ := crossCommonNeighbor G hfree hdf₁ x z₁
  let uc₂ := crossCommonNeighbor G hfree hdf₂ x z₂
  have hrb₁ : crossIntermediateComponent G hfree hef₁ y z₁ = b :=
    crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₁ y z₁ b hby₁
  have hrb₂ : crossIntermediateComponent G hfree hef₂ y z₂ = b :=
    crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₂ y z₂ b hby₂
  have hrc₁ : crossIntermediateComponent G hfree hdf₁ x z₁ = c := by
    rw [crossIntermediateComponent_reverse G hfree hdf₁ x z₁]
    exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₁.symm z₁ x c hcx₁
  have hrc₂ : crossIntermediateComponent G hfree hdf₂ x z₂ = c := by
    rw [crossIntermediateComponent_reverse G hfree hdf₂ x z₂]
    exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf₂.symm z₂ x c hcx₂
  have hub₁comp : D.connectedComponentMk ub₁ = b := by
    rw [← hrb₁]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hef₁ y z₁)
  have hub₂comp : D.connectedComponentMk ub₂ = b := by
    rw [← hrb₂]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hef₂ y z₂)
  have huc₁comp : D.connectedComponentMk uc₁ = c := by
    rw [← hrc₁]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hdf₁ x z₁)
  have huc₂comp : D.connectedComponentMk uc₂ = c := by
    rw [← hrc₂]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hdf₂ x z₂)
  change ub₁ ≠ ub₂ ∨ uc₁ ≠ uc₂
  by_contra hsame
  push Not at hsame
  have hubc : ub₁ ≠ uc₁ := by
    intro h
    exact hbc (hub₁comp.symm.trans ((congrArg D.connectedComponentMk h).trans huc₁comp))
  have hz₂ub₁ : G.Adj z₂.1 ub₁ := by
    rw [hsame.1]
    exact (crossCommonNeighbor_spec G hfree hef₂ y z₂).2
  have hz₂uc₁ : G.Adj z₂.1 uc₁ := by
    rw [hsame.2]
    exact (crossCommonNeighbor_spec G hfree hdf₂ x z₂).2
  have hubMem : ub₁ ∈ G.neighborFinset z₁.1 ∩ G.neighborFinset z₂.1 := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z₁.1 ub₁).mpr
          (crossCommonNeighbor_spec G hfree hef₁ y z₁).2,
        (G.mem_neighborFinset z₂.1 ub₁).mpr hz₂ub₁⟩
  have hucMem : uc₁ ∈ G.neighborFinset z₁.1 ∩ G.neighborFinset z₂.1 := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z₁.1 uc₁).mpr
          (crossCommonNeighbor_spec G hfree hdf₁ x z₁).2,
        (G.mem_neighborFinset z₂.1 uc₁).mpr hz₂uc₁⟩
  exact hubc (Finset.card_le_one.mp
    (card_inter_neighborFinset_le_one hfree hz) ub₁ hubMem uc₁ hucMem)

/-- Backwards-compatible form retaining the formerly superfluous hypothesis
that the two fork roots lie in different defect components. -/
theorem ownerFork_canonicalCenter_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f₁ f₂ b c :
      (secondOrderDefectGraph G).ConnectedComponent}
    (_hde : d ≠ e) (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hz : z₁.1 ≠ z₂.1)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hcx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1)
    (hcx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1) :
    let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
    let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
    let uc₁ := crossCommonNeighbor G hfree hdf₁ x z₁
    let uc₂ := crossCommonNeighbor G hfree hdf₂ x z₂
    ub₁ ≠ ub₂ ∨ uc₁ ≠ uc₂ :=
  ownerFork_canonicalCenter_separation_without_root_separation
    G hfree hef₁ hef₂ hdf₁ hdf₂ hbc x y z₁ z₂ hz hby₁ hby₂ hcx₁ hcx₂

end

end Erdos85
