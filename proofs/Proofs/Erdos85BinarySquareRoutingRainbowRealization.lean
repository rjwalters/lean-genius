import Proofs.Erdos85BinarySquareRoutingCompletionDichotomy

/-! # Realizing owner rainbows as routing completions -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every owner-colored rainbow triangle in one defect component comes from an
actual monochromatic routing completion.  The three endpoint witnesses are
the common neighbors certifying its three owner edges, and the canonical
pairwise common neighbors recover the given triangle exactly. -/
theorem ownerRainbow_exists_monochromatic_routing_completion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c d e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (y₁ y₂ y₃ : d.supp)
    (hE : (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁.1 y₂.1)
    (hF : (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂.1 y₃.1)
    (hC : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃.1 y₁.1) :
    ∃ x : c.supp, ∃ z : e.supp, ∃ w : f.supp,
      crossIntermediateComponent G hfree hce x z = d ∧
      crossIntermediateComponent G hfree hef z w = d ∧
      crossIntermediateComponent G hfree hcf x w = d ∧
      crossCommonNeighbor G hfree hce x z = y₁.1 ∧
      crossCommonNeighbor G hfree hef z w = y₂.1 ∧
      crossCommonNeighbor G hfree hcf x w = y₃.1 := by
  have hEdata := (componentOwnerGraph_adj G (secondOrderDefectGraph G) e
    y₁.1 y₂.1).mp hE
  have hFdata := (componentOwnerGraph_adj G (secondOrderDefectGraph G) f
    y₂.1 y₃.1).mp hF
  have hCdata := (componentOwnerGraph_adj G (secondOrderDefectGraph G) c
    y₃.1 y₁.1).mp hC
  rcases hEdata.2 with ⟨z₀, hz⟩
  rcases hFdata.2 with ⟨w₀, hw⟩
  rcases hCdata.2 with ⟨x₀, hx⟩
  have ⟨hz₁, hz₂⟩ := Finset.mem_inter.mp hz
  have ⟨hw₂, hw₃⟩ := Finset.mem_inter.mp hw
  have ⟨hx₃, hx₁⟩ := Finset.mem_inter.mp hx
  have hz₁data := Finset.mem_filter.mp hz₁
  have hz₂data := Finset.mem_filter.mp hz₂
  have hw₂data := Finset.mem_filter.mp hw₂
  have hw₃data := Finset.mem_filter.mp hw₃
  have hx₃data := Finset.mem_filter.mp hx₃
  have hx₁data := Finset.mem_filter.mp hx₁
  have hz₁adj : G.Adj y₁.1 z₀ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hz₁data.1
  have hz₂adj : G.Adj y₂.1 z₀ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hz₂data.1
  have hw₂adj : G.Adj y₂.1 w₀ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hw₂data.1
  have hw₃adj : G.Adj y₃.1 w₀ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hw₃data.1
  have hx₃adj : G.Adj y₃.1 x₀ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx₃data.1
  have hx₁adj : G.Adj y₁.1 x₀ := by
    simpa only [SimpleGraph.mem_neighborFinset] using hx₁data.1
  let z : e.supp := ⟨z₀, (ConnectedComponent.mem_supp_iff e z₀).2 hz₁data.2⟩
  let w : f.supp := ⟨w₀, (ConnectedComponent.mem_supp_iff f w₀).2 hw₂data.2⟩
  let x : c.supp := ⟨x₀, (ConnectedComponent.mem_supp_iff c x₀).2 hx₃data.2⟩
  have hy₁comp : (secondOrderDefectGraph G).connectedComponentMk y₁.1 = d :=
    (ConnectedComponent.mem_supp_iff d y₁.1).mp y₁.2
  have hy₂comp : (secondOrderDefectGraph G).connectedComponentMk y₂.1 = d :=
    (ConnectedComponent.mem_supp_iff d y₂.1).mp y₂.2
  have hy₃comp : (secondOrderDefectGraph G).connectedComponentMk y₃.1 = d :=
    (ConnectedComponent.mem_supp_iff d y₃.1).mp y₃.2
  have hroute₁ : crossIntermediateComponent G hfree hce x z = d := by
    rw [crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
      G hfree hce x z ⟨hx₁adj.symm, hz₁adj.symm⟩]
    exact hy₁comp
  have hroute₂ : crossIntermediateComponent G hfree hef z w = d := by
    rw [crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
      G hfree hef z w ⟨hz₂adj.symm, hw₂adj.symm⟩]
    exact hy₂comp
  have hroute₃ : crossIntermediateComponent G hfree hcf x w = d := by
    rw [crossIntermediateComponent_eq_connectedComponentMk_of_commonNeighbor
      G hfree hcf x w ⟨hx₃adj.symm, hw₃adj.symm⟩]
    exact hy₃comp
  have hcenter₁ : crossCommonNeighbor G hfree hce x z = y₁.1 := by
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hce x z
      ⟨hx₁adj.symm, hz₁adj.symm⟩
  have hcenter₂ : crossCommonNeighbor G hfree hef z w = y₂.1 := by
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hef z w
      ⟨hz₂adj.symm, hw₂adj.symm⟩
  have hcenter₃ : crossCommonNeighbor G hfree hcf x w = y₃.1 := by
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hcf x w
      ⟨hx₃adj.symm, hw₃adj.symm⟩
  exact ⟨x, z, w, hroute₁, hroute₂, hroute₃,
    hcenter₁, hcenter₂, hcenter₃⟩

end

end Erdos85
