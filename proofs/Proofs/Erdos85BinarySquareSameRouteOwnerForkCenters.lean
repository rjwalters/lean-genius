import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters

/-! # Canonical-center separation with one repeated route owner -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem exists_ownerCenter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {x y : V}
    (h : (componentOwnerGraph G D owner).Adj x y) :
    ∃ w, G.Adj x w ∧ G.Adj y w ∧ D.connectedComponentMk w = owner := by
  rw [componentOwnerGraph_adj] at h
  obtain ⟨_hxy, w, hw⟩ := h
  have hw' := Finset.mem_inter.mp hw
  have hx := Finset.mem_filter.mp hw'.1
  have hy := Finset.mem_filter.mp hw'.2
  exact ⟨w, (G.mem_neighborFinset x w).mp hx.1,
    (G.mem_neighborFinset y w).mp hy.1, hx.2⟩

/-- If the fixed root edge has owner `a` while both closing routes have owner
`b ≠ a`, the canonical `b`-centers still separate across two closings.  The
first-edge `a`-center first forces the two `b`-centers within either closing
to be distinct; otherwise the roots have two common neighbors.  Coincidence
of both center pairs across closings would then give the closings two distinct
common neighbors. -/
theorem sameRouteOwnerFork_canonicalCenter_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d f a b : (secondOrderDefectGraph G).ConnectedComponent}
    (hdf : d ≠ f) (hab : a ≠ b)
    (x y : d.supp) (z₁ z₂ : f.supp) (hz : z₁.1 ≠ z₂.1)
    (haxy : (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x.1 y.1)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hbx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj z₁.1 x.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hbx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj z₂.1 x.1) :
    let uy₁ := crossCommonNeighbor G hfree hdf y z₁
    let uy₂ := crossCommonNeighbor G hfree hdf y z₂
    let ux₁ := crossCommonNeighbor G hfree hdf x z₁
    let ux₂ := crossCommonNeighbor G hfree hdf x z₂
    uy₁ ≠ uy₂ ∨ ux₁ ≠ ux₂ := by
  classical
  let D := secondOrderDefectGraph G
  let uy₁ := crossCommonNeighbor G hfree hdf y z₁
  let uy₂ := crossCommonNeighbor G hfree hdf y z₂
  let ux₁ := crossCommonNeighbor G hfree hdf x z₁
  let ux₂ := crossCommonNeighbor G hfree hdf x z₂
  have huy₁comp : D.connectedComponentMk uy₁ = b := by
    have hr := crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf y z₁ b hby₁
    rw [← hr]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hdf y z₁)
  have hux₁comp : D.connectedComponentMk ux₁ = b := by
    have hr : crossIntermediateComponent G hfree hdf x z₁ = b := by
      rw [crossIntermediateComponent_reverse G hfree hdf x z₁]
      exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
        G hfree hdf.symm z₁ x b hbx₁
    rw [← hr]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hdf x z₁)
  obtain ⟨w, hxw, hyw, hwcomp⟩ := exists_ownerCenter G D a haxy
  have hwuy : w ≠ uy₁ := by
    intro h
    apply hab
    exact hwcomp.symm.trans ((congrArg D.connectedComponentMk h).trans huy₁comp)
  have hxy : x.1 ≠ y.1 := haxy.ne
  have huyux : uy₁ ≠ ux₁ := by
    intro hsame
    have hxuy : G.Adj x.1 uy₁ := by
      rw [hsame]
      exact (crossCommonNeighbor_spec G hfree hdf x z₁).1
    have hyuy : G.Adj y.1 uy₁ :=
      (crossCommonNeighbor_spec G hfree hdf y z₁).1
    have hwMem : w ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x.1 w).mpr hxw,
          (G.mem_neighborFinset y.1 w).mpr hyw⟩
    have huyMem : uy₁ ∈ G.neighborFinset x.1 ∩ G.neighborFinset y.1 := by
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset x.1 uy₁).mpr hxuy,
          (G.mem_neighborFinset y.1 uy₁).mpr hyuy⟩
    exact hwuy (Finset.card_le_one.mp
      (card_inter_neighborFinset_le_one hfree hxy) w hwMem uy₁ huyMem)
  change uy₁ ≠ uy₂ ∨ ux₁ ≠ ux₂
  by_contra hsame
  push Not at hsame
  have hz₂uy₁ : G.Adj z₂.1 uy₁ := by
    rw [hsame.1]
    exact (crossCommonNeighbor_spec G hfree hdf y z₂).2
  have hz₂ux₁ : G.Adj z₂.1 ux₁ := by
    rw [hsame.2]
    exact (crossCommonNeighbor_spec G hfree hdf x z₂).2
  have huyMem : uy₁ ∈ G.neighborFinset z₁.1 ∩ G.neighborFinset z₂.1 := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z₁.1 uy₁).mpr
          (crossCommonNeighbor_spec G hfree hdf y z₁).2,
        (G.mem_neighborFinset z₂.1 uy₁).mpr hz₂uy₁⟩
  have huxMem : ux₁ ∈ G.neighborFinset z₁.1 ∩ G.neighborFinset z₂.1 := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z₁.1 ux₁).mpr
          (crossCommonNeighbor_spec G hfree hdf x z₁).2,
        (G.mem_neighborFinset z₂.1 ux₁).mpr hz₂ux₁⟩
  exact huyux (Finset.card_le_one.mp
    (card_inter_neighborFinset_le_one hfree hz) uy₁ huyMem ux₁ huxMem)

end

end Erdos85

#print axioms Erdos85.sameRouteOwnerFork_canonicalCenter_separation
