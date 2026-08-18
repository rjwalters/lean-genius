import Proofs.Erdos85RoutingOwnerRainbowExactColors

/-! # Ambient hexagons carried by routing-owner rainbows -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An owner-color edge has a common ambient neighbor lying in its owner
component. -/
theorem componentOwnerGraph_adj_exists_owner_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (owner : D.ConnectedComponent) {x y : V}
    (howner : (componentOwnerGraph G D owner).Adj x y) :
    ∃ z : owner.supp, G.Adj x z.1 ∧ G.Adj y z.1 := by
  rw [componentOwnerGraph_adj] at howner
  obtain ⟨_hxy, z, hz⟩ := howner
  have hzmem := Finset.mem_inter.mp hz
  have hzx : z ∈ G.neighborFinset x ∧ D.connectedComponentMk z = owner := by
    simpa [componentNeighborFinset] using hzmem.1
  have hzy : z ∈ G.neighborFinset y ∧ D.connectedComponentMk z = owner := by
    simpa [componentNeighborFinset] using hzmem.2
  have hzSupp : z ∈ owner.supp :=
    (ConnectedComponent.mem_supp_iff owner z).mpr hzx.2
  exact ⟨⟨z, hzSupp⟩,
    (G.mem_neighborFinset x z).mp hzx.1,
    (G.mem_neighborFinset y z).mp hzy.1⟩

/-- A routing-owner rainbow lifts to an alternating ambient hexagon.  Its
three vertices in routing component `d` alternate with common-neighbor
witnesses in owner components `e`, `f`, and `c`. -/
theorem routingOwnerRainbow_exists_ambient_hexagon
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent)
    (hrainbow : routingOwnerRainbow G d e f c) :
    ∃ (y₁ y₂ y₃ : d.supp) (a : e.supp) (b : f.supp) (g : c.supp),
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      G.Adj y₁.1 a.1 ∧ G.Adj y₂.1 a.1 ∧
      G.Adj y₂.1 b.1 ∧ G.Adj y₃.1 b.1 ∧
      G.Adj y₃.1 g.1 ∧ G.Adj y₁.1 g.1 := by
  obtain ⟨y₁, y₂, y₃, h12, h23, h31, he, hf, hc⟩ := hrainbow
  obtain ⟨a, hy₁a, hy₂a⟩ :=
    componentOwnerGraph_adj_exists_owner_commonNeighbor
      G (secondOrderDefectGraph G) e he
  obtain ⟨b, hy₂b, hy₃b⟩ :=
    componentOwnerGraph_adj_exists_owner_commonNeighbor
      G (secondOrderDefectGraph G) f hf
  obtain ⟨g, hy₃g, hy₁g⟩ :=
    componentOwnerGraph_adj_exists_owner_commonNeighbor
      G (secondOrderDefectGraph G) c hc
  exact ⟨y₁, y₂, y₃, a, b, g, h12, h23, h31,
    hy₁a, hy₂a, hy₂b, hy₃b, hy₃g, hy₁g⟩

end

end Erdos85
