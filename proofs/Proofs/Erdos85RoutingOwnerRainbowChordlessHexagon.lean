import Proofs.Erdos85RoutingOwnerRainbowHexagon

/-! # Forbidden short diagonals of routing-rainbow hexagons -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem coe_ne_of_mem_distinct_components
    {V : Type*} (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    {c e : D.ConnectedComponent} (hce : c ≠ e)
    (x : c.supp) (y : e.supp) : x.1 ≠ y.1 := by
  intro hxy
  have hx : D.connectedComponentMk x.1 = c :=
    (ConnectedComponent.mem_supp_iff c x.1).mp x.2
  have hy : D.connectedComponentMk y.1 = e :=
    (ConnectedComponent.mem_supp_iff e y.1).mp y.2
  exact hce (hx.symm.trans ((congrArg D.connectedComponentMk hxy).trans hy))

/-- When the three owner colors are distinct, C4-freeness forbids the three
short diagonals of the ambient rainbow hexagon. -/
theorem routingOwnerRainbow_exists_ambient_hexagon_forbidden_shortDiagonals
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent)
    (hef : e ≠ f) (hfc : f ≠ c) (hce : c ≠ e)
    (hrainbow : routingOwnerRainbow G d e f c) :
    ∃ (y₁ y₂ y₃ : d.supp) (a : e.supp) (b : f.supp) (g : c.supp),
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      G.Adj y₁.1 a.1 ∧ G.Adj y₂.1 a.1 ∧
      G.Adj y₂.1 b.1 ∧ G.Adj y₃.1 b.1 ∧
      G.Adj y₃.1 g.1 ∧ G.Adj y₁.1 g.1 ∧
      ¬ G.Adj y₁.1 b.1 ∧ ¬ G.Adj y₂.1 g.1 ∧ ¬ G.Adj y₃.1 a.1 := by
  obtain ⟨y₁, y₂, y₃, a, b, g, h12, h23, h31,
      hy₁a, hy₂a, hy₂b, hy₃b, hy₃g, hy₁g⟩ :=
    routingOwnerRainbow_exists_ambient_hexagon G d e f c hrainbow
  have hab : a.1 ≠ b.1 := coe_ne_of_mem_distinct_components
    (secondOrderDefectGraph G) hef a b
  have hbg : b.1 ≠ g.1 := coe_ne_of_mem_distinct_components
    (secondOrderDefectGraph G) hfc b g
  have hga : g.1 ≠ a.1 := coe_ne_of_mem_distinct_components
    (secondOrderDefectGraph G) hce g a
  have hn₁b : ¬ G.Adj y₁.1 b.1 := by
    intro hy₁b
    apply hfree
    exact containsC4_of_two_common
      (fun h => h31 (Subtype.ext h.symm)) hbg
      hy₁b.symm hy₃b.symm hy₁g.symm hy₃g.symm
  have hn₂g : ¬ G.Adj y₂.1 g.1 := by
    intro hy₂g
    apply hfree
    exact containsC4_of_two_common
      (fun h => h12 (Subtype.ext h.symm)) hga
      hy₂g.symm hy₁g.symm hy₂a.symm hy₁a.symm
  have hn₃a : ¬ G.Adj y₃.1 a.1 := by
    intro hy₃a
    apply hfree
    exact containsC4_of_two_common
      (fun h => h23 (Subtype.ext h.symm)) hab
      hy₃a.symm hy₂a.symm hy₃b.symm hy₂b.symm
  exact ⟨y₁, y₂, y₃, a, b, g, h12, h23, h31,
    hy₁a, hy₂a, hy₂b, hy₃b, hy₃g, hy₁g, hn₁b, hn₂g, hn₃a⟩

end

end Erdos85
