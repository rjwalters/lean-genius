import Proofs.Erdos85RoutingOwnerRainbowSelectorTriangle

/-! # Exact owner colors on routing-rainbow triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Once a pair has a specified owner edge, uniqueness of the common-neighbor
component identifies every other possible owner color with that one. -/
theorem componentOwnerGraph_adj_iff_owner_eq_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {x y : V} (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x y)
    (owner' : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentOwnerGraph G (secondOrderDefectGraph G) owner').Adj x y ↔
      owner' = owner := by
  have hxy : x ≠ y := by
    exact ((componentOwnerGraph_adj G (secondOrderDefectGraph G) owner x y).mp
      howner).1
  have hnotD := componentOwnerGraph_adj_not_secondOrderDefect_adj
    G hfree owner howner
  obtain ⟨u, hu, huniq⟩ :=
    (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
      G hfree hxy).mp hnotD
  constructor
  · intro howner'
    exact (huniq owner' howner').trans (huniq owner howner).symm
  · rintro rfl
    exact howner

/-- A routing-owner rainbow is an exactly colored selector-complement
triangle: each edge belongs to its displayed owner graph and to no other. -/
theorem routingOwnerRainbow_exists_exactlyColored_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent)
    (hrainbow : routingOwnerRainbow G d e f c) :
    ∃ y₁ y₂ y₃ : d.supp,
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      (∀ owner, (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj
        y₁.1 y₂.1 ↔ owner = e) ∧
      (∀ owner, (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj
        y₂.1 y₃.1 ↔ owner = f) ∧
      (∀ owner, (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj
        y₃.1 y₁.1 ↔ owner = c) := by
  obtain ⟨y₁, y₂, y₃, h12, h23, h31, he, hf, hc⟩ := hrainbow
  refine ⟨y₁, y₂, y₃, h12, h23, h31, ?_, ?_, ?_⟩
  · intro owner
    exact componentOwnerGraph_adj_iff_owner_eq_of_adj G hfree e he owner
  · intro owner
    exact componentOwnerGraph_adj_iff_owner_eq_of_adj G hfree f hf owner
  · intro owner
    exact componentOwnerGraph_adj_iff_owner_eq_of_adj G hfree c hc owner

end

end Erdos85
