import Proofs.Erdos85OrderSixtyFourRoutingCensusDichotomy

/-! # Owner-rainbow triangles are selector-complement triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every owner-color edge is a nonedge of the second-order defect graph. -/
theorem componentOwnerGraph_adj_not_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V}
    (howner : (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x y) :
    ¬ (secondOrderDefectGraph G).Adj x y := by
  rw [componentOwnerGraph_adj] at howner
  obtain ⟨hxy, z, hz⟩ := howner
  have hzmem := Finset.mem_inter.mp hz
  have hzx : G.Adj x z := by
    exact (G.mem_neighborFinset x z).mp
      (Finset.mem_filter.mp hzmem.1).1
  have hzy : G.Adj y z := by
    exact (G.mem_neighborFinset y z).mp
      (Finset.mem_filter.mp hzmem.2).1
  exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hxy hzx hzy

/-- Forgetting its owner colors, a routing-owner rainbow is a triangle in
the complement of the defect graph induced on its routing component. -/
theorem routingOwnerRainbow_exists_selectorComplement_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent)
    (hrainbow : routingOwnerRainbow G d e f c) :
    ∃ y₁ y₂ y₃ : d.supp,
      (((secondOrderDefectGraph G).induce d.supp)ᶜ).Adj y₁ y₂ ∧
      (((secondOrderDefectGraph G).induce d.supp)ᶜ).Adj y₂ y₃ ∧
      (((secondOrderDefectGraph G).induce d.supp)ᶜ).Adj y₃ y₁ := by
  obtain ⟨y₁, y₂, y₃, h12, h23, h31, he, hf, hc⟩ := hrainbow
  have hn12 := componentOwnerGraph_adj_not_secondOrderDefect_adj
    G hfree e he
  have hn23 := componentOwnerGraph_adj_not_secondOrderDefect_adj
    G hfree f hf
  have hn31 := componentOwnerGraph_adj_not_secondOrderDefect_adj
    G hfree c hc
  refine ⟨y₁, y₂, y₃, ?_, ?_, ?_⟩
  · simpa [SimpleGraph.compl_adj, SimpleGraph.induce_adj] using And.intro h12 hn12
  · simpa [SimpleGraph.compl_adj, SimpleGraph.induce_adj] using And.intro h23 hn23
  · simpa [SimpleGraph.compl_adj, SimpleGraph.induce_adj] using And.intro h31 hn31

end

end Erdos85
