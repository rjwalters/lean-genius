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

/-- The endpoint triple realizing a fixed owner rainbow is unique.  Thus the
owner-rainbow/routing-completion bridge loses no multiplicity in either
direction and is suitable for exact counting. -/
theorem ownerRainbow_existsUnique_routing_endpointTriple
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c d e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (y₁ y₂ y₃ : d.supp)
    (h12 : y₁ ≠ y₂) (h23 : y₂ ≠ y₃) (h31 : y₃ ≠ y₁)
    (hE : (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁.1 y₂.1)
    (hF : (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂.1 y₃.1)
    (hC : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃.1 y₁.1) :
    ∃! p : c.supp × (e.supp × f.supp),
      crossCommonNeighbor G hfree hce p.1 p.2.1 = y₁.1 ∧
      crossCommonNeighbor G hfree hef p.2.1 p.2.2 = y₂.1 ∧
      crossCommonNeighbor G hfree hcf p.1 p.2.2 = y₃.1 := by
  obtain ⟨x, z, w, _hr₁, _hr₂, _hr₃, hy₁, hy₂, hy₃⟩ :=
    ownerRainbow_exists_monochromatic_routing_completion
      G hfree hce hef hcf y₁ y₂ y₃ hE hF hC
  refine ⟨(x, (z, w)), ⟨hy₁, hy₂, hy₃⟩, ?_⟩
  rintro ⟨x', z', w'⟩ ⟨hy₁', hy₂', hy₃'⟩
  have unique_common {a b u v : V} (hab : a ≠ b)
      (hau : G.Adj a u) (hbu : G.Adj b u)
      (hav : G.Adj a v) (hbv : G.Adj b v) : u = v := by
    by_contra huv
    exact hfree (containsC4_of_rim hau hbu.symm hbv hav.symm hab huv
      (G.ne_of_adj hau).symm (G.ne_of_adj hbu).symm
      (G.ne_of_adj hav).symm (G.ne_of_adj hbv).symm)
  have hxz := crossCommonNeighbor_spec G hfree hce x z
  have hzw := crossCommonNeighbor_spec G hfree hef z w
  have hxw := crossCommonNeighbor_spec G hfree hcf x w
  have hxz' := crossCommonNeighbor_spec G hfree hce x' z'
  have hzw' := crossCommonNeighbor_spec G hfree hef z' w'
  have hxw' := crossCommonNeighbor_spec G hfree hcf x' w'
  rw [hy₁] at hxz
  rw [hy₂] at hzw
  rw [hy₃] at hxw
  rw [hy₁'] at hxz'
  rw [hy₂'] at hzw'
  rw [hy₃'] at hxw'
  have ex : x = x' := by
    apply Subtype.ext
    exact unique_common (show y₃.1 ≠ y₁.1 from fun h => h31 (Subtype.ext h))
      hxw.1.symm hxz.1.symm hxw'.1.symm hxz'.1.symm
  have ez : z = z' := by
    apply Subtype.ext
    exact unique_common (show y₁.1 ≠ y₂.1 from fun h => h12 (Subtype.ext h))
      hxz.2.symm hzw.1.symm hxz'.2.symm hzw'.1.symm
  have ew : w = w' := by
    apply Subtype.ext
    exact unique_common (show y₂.1 ≠ y₃.1 from fun h => h23 (Subtype.ext h))
      hzw.2.symm hxw.2.symm hzw'.2.symm hxw'.2.symm
  subst x'
  subst z'
  subst w'
  rfl

end

end Erdos85
