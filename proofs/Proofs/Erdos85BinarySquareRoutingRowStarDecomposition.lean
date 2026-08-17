import Proofs.Erdos85BinarySquareRoutingStarCompletions
import Proofs.Erdos85BinarySquareSeparatedCentersDisjointSelectors

/-! # Every routing row is its canonical star decomposition -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A fixed-color routing row from `x` into `e` is exactly the union of the
`e`-neighbor rows of the component-`c` neighbors of `x`.  This requires only
unique cross-component routing, not regularity or size-two hypotheses. -/
theorem routingRow_eq_biUnion_componentCrossNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (c : (secondOrderDefectGraph G).ConnectedComponent)
    (x : d.supp) :
    ((Finset.univ : Finset e.supp).filter fun w =>
      c = crossIntermediateComponent G hfree hde x w) =
      (componentCrossNeighborFinset G c x).biUnion fun u =>
        componentCrossNeighborFinset G e u := by
  classical
  ext w
  constructor
  · intro hw
    have hroute := (Finset.mem_filter.mp hw).2
    let u₀ := crossCommonNeighbor G hfree hde x w
    have hu₀memRoute := crossCommonNeighbor_mem_intermediate G hfree hde x w
    have hu₀mem : u₀ ∈ c.supp := by
      apply (ConnectedComponent.mem_supp_iff c u₀).mpr
      have hucomp := (ConnectedComponent.mem_supp_iff
        (crossIntermediateComponent G hfree hde x w) u₀).mp hu₀memRoute
      exact hucomp.trans hroute.symm
    let u : c.supp := ⟨u₀, hu₀mem⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨u, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (crossCommonNeighbor_spec G hfree hde x w).1⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (crossCommonNeighbor_spec G hfree hde x w).2.symm⟩
  · intro hw
    obtain ⟨u, hux, huw⟩ := Finset.mem_biUnion.mp hw
    have huxAdj : G.Adj x.1 u.1 := (Finset.mem_filter.mp hux).2
    have huwAdj : G.Adj u.1 w.1 := (Finset.mem_filter.mp huw).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    symm
    calc
      crossIntermediateComponent G hfree hde x w =
          (secondOrderDefectGraph G).connectedComponentMk u.1 :=
        crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
          G hfree hde x w ⟨huxAdj, huwAdj.symm⟩
      _ = c := (ConnectedComponent.mem_supp_iff c u.1).mp u.2

/-- The star rows occurring in the canonical routing-row decomposition are
pairwise disjoint.  Thus in the size-two regime the familiar "two stars
saturate a four-point routing row" conclusion is the generic decomposition
of every routing row, rather than an exceptional terminal configuration. -/
theorem routingRow_starRows_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e c : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x : d.supp)
    {u₁ u₂ : c.supp}
    (hu₁ : u₁ ∈ componentCrossNeighborFinset G c x)
    (hu₂ : u₂ ∈ componentCrossNeighborFinset G c x)
    (hne : u₁ ≠ u₂) :
    Disjoint (componentCrossNeighborFinset G e u₁)
      (componentCrossNeighborFinset G e u₂) := by
  have hxcomp :
      (secondOrderDefectGraph G).connectedComponentMk x.1 = d :=
    (ConnectedComponent.mem_supp_iff d x.1).mp x.2
  have hxoutside :
      (secondOrderDefectGraph G).connectedComponentMk x.1 ≠ e := by
    rw [hxcomp]
    exact hde
  exact componentCrossNeighborFinset_disjoint_of_distinct_sharedNeighbor_outside
    G hfree u₁ u₂ hne (Finset.mem_filter.mp hu₁).2.symm
      (Finset.mem_filter.mp hu₂).2.symm hxoutside

/-- Star rows belonging to *different* routing colors at the same root are
also disjoint.  This is the first compatibility law between the canonical
decompositions of distinct routing rows: all their centers share the root,
so a target point common to two stars would create a four-cycle. -/
theorem routingRow_crossColor_starRows_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e c f : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hcf : c ≠ f) (x : d.supp)
    (u : c.supp) (v : f.supp)
    (hu : u ∈ componentCrossNeighborFinset G c x)
    (hv : v ∈ componentCrossNeighborFinset G f x) :
    Disjoint (componentCrossNeighborFinset G e u)
      (componentCrossNeighborFinset G e v) := by
  classical
  have huv : u.1 ≠ v.1 := by
    intro huv
    apply hcf
    have huc :
        (secondOrderDefectGraph G).connectedComponentMk u.1 = c :=
      (ConnectedComponent.mem_supp_iff c u.1).mp u.2
    have hvf :
        (secondOrderDefectGraph G).connectedComponentMk v.1 = f :=
      (ConnectedComponent.mem_supp_iff f v.1).mp v.2
    exact huc.symm.trans ((congrArg
      (secondOrderDefectGraph G).connectedComponentMk huv).trans hvf)
  have hxoutside :
      (secondOrderDefectGraph G).connectedComponentMk x.1 ≠ e := by
    rw [(ConnectedComponent.mem_supp_iff d x.1).mp x.2]
    exact hde
  have hamb := componentNeighborFinset_disjoint_of_distinct_sharedNeighbor_outside
    G (secondOrderDefectGraph G) hfree e huv
      (Finset.mem_filter.mp hu).2.symm (Finset.mem_filter.mp hv).2.symm hxoutside
  rw [Finset.disjoint_left]
  intro w hwu hwv
  apply Finset.disjoint_left.mp hamb
  · rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset u.1 w.1).mpr (Finset.mem_filter.mp hwu).2,
      (ConnectedComponent.mem_supp_iff e w.1).mp w.2⟩
  · rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset v.1 w.1).mpr (Finset.mem_filter.mp hwv).2,
      (ConnectedComponent.mem_supp_iff e w.1).mp w.2⟩

end

end Erdos85
