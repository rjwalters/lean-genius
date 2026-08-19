import Proofs.Erdos85SizeTwoMuNegThreePairOwnerTrichotomy

/-! # Triangle-free edges as ambient defect edges -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In a `C₄`-free graph, an ambient edge is triangle-free exactly when it
is also a second-order defect edge. -/
theorem triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    triangleFreeEdgeGraph G = G ⊓ secondOrderDefectGraph G := by
  ext x y
  constructor
  · intro hxy
    have hdata := (mem_triangleFreeNeighbors G x y).mp hxy
    exact ⟨hdata.1,
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree
        (G.ne_of_adj hdata.1)).mpr hdata.2⟩
  · rintro ⟨hG, hD⟩
    exact (mem_triangleFreeNeighbors G x y).mpr ⟨hG,
      (secondOrderDefectGraph_adj_iff_card_common_eq_zero G hfree
        (G.ne_of_adj hG)).mp hD⟩

/-- In the coherent `mu=-3` normal form, the three cross nondefect
matchings are precisely the positions at which an internal ambient edge is
triangle-bearing. Every other internal ambient edge is triangle-free. -/
theorem MuNegThreeCrossOwnerNormalForm.internal_edge_triangle_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (s : V → ℤ)
    (N : MuNegThreeCrossOwnerNormalForm G c s) :
    (∀ x y,
      (triangleFreeEdgeGraph G).Adj x.1 y.1 ↔
        G.Adj x.1 y.1 ∧
          ¬ (y = N.f x ∨ y = N.f (N.σ x) ∨ y = N.f (N.τ x))) ∧
    ∀ x y,
      G.Adj x.1 y.1 ∧ ¬ (triangleFreeEdgeGraph G).Adj x.1 y.1 ↔
        G.Adj x.1 y.1 ∧
          (y = N.f x ∨ y = N.f (N.σ x) ∨ y = N.f (N.τ x)) := by
  have hgraph := triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph G hfree
  constructor
  · intro x y
    have hDnot : (secondOrderDefectGraph G).Adj x.1 y.1 ↔
        ¬ (y = N.f x ∨ y = N.f (N.σ x) ∨ y = N.f (N.τ x)) := by
      constructor
      · intro hD hmatch
        exact (N.exhaust x y).mpr hmatch hD
      · intro hmatch
        by_contra hD
        exact hmatch ((N.exhaust x y).mp hD)
    rw [hgraph]
    exact and_congr_right fun _ ↦ hDnot
  · intro x y
    have htf : (triangleFreeEdgeGraph G).Adj x.1 y.1 ↔
        G.Adj x.1 y.1 ∧
          ¬ (y = N.f x ∨ y = N.f (N.σ x) ∨ y = N.f (N.τ x)) := by
      rw [hgraph]
      apply and_congr_right
      intro _
      constructor
      · intro hD hmatch
        exact (N.exhaust x y).mpr hmatch hD
      · intro hmatch
        by_contra hD
        exact hmatch ((N.exhaust x y).mp hD)
    constructor
    · rintro ⟨hG, hnot⟩
      refine ⟨hG, ?_⟩
      by_contra hmatch
      exact hnot (htf.mpr ⟨hG, hmatch⟩)
    · rintro ⟨hG, hmatch⟩
      refine ⟨hG, ?_⟩
      intro htfxy
      exact (htf.mp htfxy).2 hmatch

end

end Erdos85

#print axioms Erdos85.triangleFreeEdgeGraph_eq_inf_secondOrderDefectGraph
#print axioms Erdos85.MuNegThreeCrossOwnerNormalForm.internal_edge_triangle_split
