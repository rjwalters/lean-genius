import Proofs.Erdos85BinarySquareCrossRoutingSymmetry

/-! # Lifting routing triangles to ambient common neighbors -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The unique ambient common neighbor of vertices in distinct defect
components. -/
def crossCommonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) : V :=
  Classical.choose
    (existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hce x z)

/-- The chosen cross common neighbor is adjacent to both endpoints. -/
theorem crossCommonNeighbor_spec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    G.Adj x.1 (crossCommonNeighbor G hfree hce x z) ∧
      G.Adj z.1 (crossCommonNeighbor G hfree hce x z) :=
  (Classical.choose_spec
    (existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hce x z)).1

/-- Any ambient common neighbor of the two endpoints is the chosen one. -/
theorem eq_crossCommonNeighbor_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) {y : V}
    (hy : G.Adj x.1 y ∧ G.Adj z.1 y) :
    y = crossCommonNeighbor G hfree hce x z :=
  (Classical.choose_spec
    (existsUnique_common_neighbor_of_mem_distinct_secondOrderDefect_components
      G hfree hce x z)).2 y hy

/-- The chosen common neighbor belongs to the routing component. -/
theorem crossCommonNeighbor_mem_intermediate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (x : c.supp) (z : e.supp) :
    crossCommonNeighbor G hfree hce x z ∈
      (crossIntermediateComponent G hfree hce x z).supp := by
  obtain ⟨y, hy, _hyuniq⟩ :=
    crossIntermediateComponent_spec G hfree hce x z
  have heq : y.1 = crossCommonNeighbor G hfree hce x z :=
    eq_crossCommonNeighbor_of_adj G hfree hce x z hy
  rw [← heq]
  exact y.2

private theorem componentOwnerGraph_adj_of_common_neighbor_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {a b u : V}
    (hab : a ≠ b) (hau : G.Adj a u) (hbu : G.Adj b u)
    (hu : u ∈ owner.supp) :
    (componentOwnerGraph G D owner).Adj a b := by
  rw [componentOwnerGraph_adj]
  refine ⟨hab, ⟨u, ?_⟩⟩
  simp only [Finset.mem_inter, componentNeighborFinset, Finset.mem_filter,
    SimpleGraph.mem_neighborFinset]
  have hucomp : D.connectedComponentMk u = owner :=
    (ConnectedComponent.mem_supp_iff owner u).mp hu
  exact ⟨⟨hau, hucomp⟩, ⟨hbu, hucomp⟩⟩

/-- A monochromatic routing triangle lifts in exactly two structural ways.
Its three pairwise common neighbors either coincide in one shared center, or
are pairwise distinct and form a rainbow triangle in the owner factors of the
routing component. -/
theorem monochromatic_routing_triangle_commonNeighbor_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e f d : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (x : c.supp) (z : e.supp) (w : f.supp)
    (h₁ : crossIntermediateComponent G hfree hce x z = d)
    (h₂ : crossIntermediateComponent G hfree hef z w = d)
    (h₃ : crossIntermediateComponent G hfree hcf x w = d) :
    ∃ y₁ y₂ y₃ : V,
      G.Adj x.1 y₁ ∧ G.Adj z.1 y₁ ∧
      G.Adj z.1 y₂ ∧ G.Adj w.1 y₂ ∧
      G.Adj x.1 y₃ ∧ G.Adj w.1 y₃ ∧
      (secondOrderDefectGraph G).connectedComponentMk y₁ = d ∧
      (secondOrderDefectGraph G).connectedComponentMk y₂ = d ∧
      (secondOrderDefectGraph G).connectedComponentMk y₃ = d ∧
      ((y₁ = y₂ ∧ y₂ = y₃) ∨
        (y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
          (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁ y₂ ∧
          (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂ y₃ ∧
          (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃ y₁)) := by
  let y₁ := crossCommonNeighbor G hfree hce x z
  let y₂ := crossCommonNeighbor G hfree hef z w
  let y₃ := crossCommonNeighbor G hfree hcf x w
  have hy₁ := crossCommonNeighbor_spec G hfree hce x z
  have hy₂ := crossCommonNeighbor_spec G hfree hef z w
  have hy₃ := crossCommonNeighbor_spec G hfree hcf x w
  have hy₁mem := crossCommonNeighbor_mem_intermediate G hfree hce x z
  have hy₂mem := crossCommonNeighbor_mem_intermediate G hfree hef z w
  have hy₃mem := crossCommonNeighbor_mem_intermediate G hfree hcf x w
  have hy₁comp : (secondOrderDefectGraph G).connectedComponentMk y₁ = d := by
    rw [← h₁]
    exact (ConnectedComponent.mem_supp_iff _ _).mp hy₁mem
  have hy₂comp : (secondOrderDefectGraph G).connectedComponentMk y₂ = d := by
    rw [← h₂]
    exact (ConnectedComponent.mem_supp_iff _ _).mp hy₂mem
  have hy₃comp : (secondOrderDefectGraph G).connectedComponentMk y₃ = d := by
    rw [← h₃]
    exact (ConnectedComponent.mem_supp_iff _ _).mp hy₃mem
  refine ⟨y₁, y₂, y₃, hy₁.1, hy₁.2, hy₂.1, hy₂.2,
    hy₃.1, hy₃.2, hy₁comp, hy₂comp, hy₃comp, ?_⟩
  by_cases h12 : y₁ = y₂
  · left
    refine ⟨h12, ?_⟩
    have hcommon : G.Adj x.1 y₂ ∧ G.Adj w.1 y₂ := by
      exact ⟨h12 ▸ hy₁.1, hy₂.2⟩
    exact eq_crossCommonNeighbor_of_adj G hfree hcf x w hcommon
  · right
    have h23 : y₂ ≠ y₃ := by
      intro h
      have hcommon : G.Adj x.1 y₂ ∧ G.Adj z.1 y₂ := by
        exact ⟨h ▸ hy₃.1, hy₂.1⟩
      have heq := eq_crossCommonNeighbor_of_adj G hfree hce x z hcommon
      exact h12 heq.symm
    have h31 : y₃ ≠ y₁ := by
      intro h
      have hcommon : G.Adj z.1 y₃ ∧ G.Adj w.1 y₃ := by
        exact ⟨h ▸ hy₁.2, hy₃.2⟩
      have heq := eq_crossCommonNeighbor_of_adj G hfree hef z w hcommon
      exact h23 heq.symm
    have hzmem : z.1 ∈ e.supp := z.2
    have hwmem : w.1 ∈ f.supp := w.2
    have hxmem : x.1 ∈ c.supp := x.2
    refine ⟨h12, h23, h31, ?_, ?_, ?_⟩
    · exact componentOwnerGraph_adj_of_common_neighbor_mem
        G (secondOrderDefectGraph G) e h12 hy₁.2.symm hy₂.1.symm hzmem
    · exact componentOwnerGraph_adj_of_common_neighbor_mem
        G (secondOrderDefectGraph G) f h23 hy₂.2.symm hy₃.2.symm hwmem
    · exact componentOwnerGraph_adj_of_common_neighbor_mem
        G (secondOrderDefectGraph G) c h31 hy₃.1.symm hy₁.1.symm hxmem

end

end Erdos85
