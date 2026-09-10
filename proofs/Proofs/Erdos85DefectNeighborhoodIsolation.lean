import Proofs.Erdos85ExteriorDefectDecomposition

/-! C4-sensitive isolation for mixed fifth-moment bounds. This actual graph
statement does not require regularity; small extremal tables and aggregate
triangle-allocation bounds remain separate. -/
namespace Erdos85
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every edge inside a defect neighborhood avoids the original neighbors
of its center, on both endpoints. -/
theorem defect_neighborhood_edge_avoids_root_neighbors
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {v x y : V}
    (hvx : (secondOrderDefectGraph G).Adj v x)
    (hvy : (secondOrderDefectGraph G).Adj v y)
    (hxy : G.Adj x y) : ¬ G.Adj v x ∧ ¬ G.Adj v y := by
  have no_common {a b c : V} (hab : (secondOrderDefectGraph G).Adj a b)
      (hac : G.Adj a c) (hbc : G.Adj b c) : False := by
    have hz := (secondOrderDefectGraph_adj_iff_card_common_eq_zero
      G hfree hab.ne).mp hab
    have hempty := Finset.card_eq_zero.mp hz
    have hm : c ∈ G.neighborFinset a ∩ G.neighborFinset b := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hac, hbc⟩
    rw [hempty] at hm
    exact Finset.notMem_empty c hm
  exact ⟨fun h => no_common hvy h hxy.symm,
    fun h => no_common hvx h hxy⟩

/-- Removing the center's original neighbors loses no edges from its defect
neighborhood. The right side exposes the smaller vertex set for extremal bounds. -/
theorem defect_neighborhood_edge_iff_sdiff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (v x y : V) :
    (G.Adj x y ∧ (secondOrderDefectGraph G).Adj v x ∧
      (secondOrderDefectGraph G).Adj v y) ↔
    (G.Adj x y ∧
      x ∈ (secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v ∧
      y ∈ (secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v) := by
  simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨hxy, hvx, hvy⟩
    obtain ⟨hnx, hny⟩ := defect_neighborhood_edge_avoids_root_neighbors
      G hfree hvx hvy hxy
    exact ⟨hxy, ⟨hvx, hnx⟩, ⟨hvy, hny⟩⟩
  · rintro ⟨hxy, ⟨hvx, _⟩, ⟨hvy, _⟩⟩
    exact ⟨hxy, hvx, hvy⟩
end Erdos85
