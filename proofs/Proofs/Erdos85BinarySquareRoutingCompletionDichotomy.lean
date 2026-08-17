import Proofs.Erdos85BinarySquareRoutingTriangleLift
import Proofs.Erdos85BinarySquareRoutingStarCompletions

/-! # Canonical star/rainbow classification of routing completions -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A third endpoint lies in the direct edge's star core exactly when its
pairwise common neighbor with the left endpoint is the direct center. -/
theorem adj_crossCommonNeighbor_iff_crossCommonNeighbor_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hcf : c ≠ f)
    (x : c.supp) (z : e.supp) (w : f.supp) :
    G.Adj z.1 (crossCommonNeighbor G hfree hcf x w) ↔
      crossCommonNeighbor G hfree hce x z =
        crossCommonNeighbor G hfree hcf x w := by
  constructor
  · intro hz
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hce x z
      ⟨(crossCommonNeighbor_spec G hfree hcf x w).1, hz⟩
  · intro h
    rw [← h]
    exact (crossCommonNeighbor_spec G hfree hce x z).2

/-- Every monochromatic completion is canonically either a star completion
through the direct edge's common-neighbor center, or a rainbow owner
completion.  Unlike the existential lift theorem, this statement names the
three canonical common neighbors themselves. -/
theorem monochromatic_routing_completion_star_or_rainbow
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
    let y₁ := crossCommonNeighbor G hfree hce x z
    let y₂ := crossCommonNeighbor G hfree hef z w
    let y₃ := crossCommonNeighbor G hfree hcf x w
    (G.Adj z.1 y₃ ∧ y₁ = y₂ ∧ y₂ = y₃) ∨
      (y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁ y₂ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂ y₃ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃ y₁) := by
  dsimp only
  obtain ⟨y₁, y₂, y₃, hxy₁, hzy₁, hzy₂, hwy₂, hxy₃, hwy₃,
      _hy₁comp, _hy₂comp, _hy₃comp, hcases⟩ :=
    monochromatic_routing_triangle_commonNeighbor_dichotomy
      G hfree hce hef hcf x z w h₁ h₂ h₃
  have ey₁ : y₁ = crossCommonNeighbor G hfree hce x z :=
    eq_crossCommonNeighbor_of_adj G hfree hce x z ⟨hxy₁, hzy₁⟩
  have ey₂ : y₂ = crossCommonNeighbor G hfree hef z w :=
    eq_crossCommonNeighbor_of_adj G hfree hef z w ⟨hzy₂, hwy₂⟩
  have ey₃ : y₃ = crossCommonNeighbor G hfree hcf x w :=
    eq_crossCommonNeighbor_of_adj G hfree hcf x w ⟨hxy₃, hwy₃⟩
  rw [ey₁, ey₂, ey₃] at hcases
  rcases hcases with hstar | hrainbow
  · left
    refine ⟨?_, hstar⟩
    have hz₂ := (crossCommonNeighbor_spec G hfree hef z w).1
    exact hstar.2 ▸ hz₂
  · exact Or.inr hrainbow

/-- The two alternatives above are disjoint: a star completion cannot have
pairwise distinct canonical common neighbors. -/
theorem monochromatic_routing_completion_not_star_and_rainbow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (x : c.supp) (z : e.supp) (w : f.supp)
    (hstar : G.Adj z.1 (crossCommonNeighbor G hfree hcf x w)) :
    ¬ (crossCommonNeighbor G hfree hce x z ≠
          crossCommonNeighbor G hfree hef z w ∧
        crossCommonNeighbor G hfree hef z w ≠
          crossCommonNeighbor G hfree hcf x w ∧
        crossCommonNeighbor G hfree hcf x w ≠
          crossCommonNeighbor G hfree hce x z) := by
  intro hrainbow
  have hy₁ : crossCommonNeighbor G hfree hce x z =
      crossCommonNeighbor G hfree hcf x w := by
    symm
    exact eq_crossCommonNeighbor_of_adj G hfree hce x z
      ⟨(crossCommonNeighbor_spec G hfree hcf x w).1, hstar⟩
  exact hrainbow.2.2 hy₁.symm

end

end Erdos85
