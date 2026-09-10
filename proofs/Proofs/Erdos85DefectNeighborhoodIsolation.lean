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
/-- The surviving vertices control the entire induced edge count. This bound
is sharp enough for the zero-, one-, and two-vertex cases in the q7 cut. -/
theorem defect_neighborhood_edges_le_surviving_choose_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (v : V) :
    (G.induce (↑((secondOrderDefectGraph G).neighborFinset v) : Set V)).edgeFinset.card ≤
      (((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card).choose 2 := by
  classical
  let N : Set V := ↑((secondOrderDefectGraph G).neighborFinset v)
  let H := G.induce N
  let S : Set N := {x | ¬ G.Adj v x.1}
  have hsupport : H.support ⊆ S := by
    intro x hx
    obtain ⟨y, hxy⟩ := H.mem_support.mp hx
    have hvx : (secondOrderDefectGraph G).Adj v x.1 := by
      simpa [N] using x.2
    have hvy : (secondOrderDefectGraph G).Adj v y.1 := by
      simpa [N] using y.2
    exact (defect_neighborhood_edge_avoids_root_neighbors G hfree hvx hvy hxy).1
  let f : S → ↥((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v) :=
    fun x => ⟨x.1.1, by
      simp only [Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
      exact ⟨by simpa [N] using x.1.2, x.2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    have hv := congrArg (fun z : ↥((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v) => z.val) h
    exact hv
  have hcard : Fintype.card S ≤
      ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_le_of_injective f hf
  change H.edgeFinset.card ≤ _
  rw [← H.card_edgeFinset_induce_of_support_subset hsupport]
  exact (H.induce S).card_edgeFinset_le_card_choose_two.trans
    (Nat.choose_le_choose 2 hcard)

/-- At most two surviving vertices permit at most one induced edge. -/
theorem defect_neighborhood_edges_le_one_of_surviving_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (hsize : ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 2) :
    (G.induce (↑((secondOrderDefectGraph G).neighborFinset v) : Set V)).edgeFinset.card ≤ 1 := by
  have h := defect_neighborhood_edges_le_surviving_choose_two G hfree v
  have hc := Nat.choose_le_choose 2 hsize
  norm_num at hc
  exact h.trans hc

/-- With at most one surviving vertex, the defect neighborhood has no edges. -/
theorem defect_neighborhood_edges_eq_zero_of_surviving_le_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (hsize : ((secondOrderDefectGraph G).neighborFinset v \ G.neighborFinset v).card ≤ 1) :
    (G.induce (↑((secondOrderDefectGraph G).neighborFinset v) : Set V)).edgeFinset.card = 0 := by
  have h := defect_neighborhood_edges_le_surviving_choose_two G hfree v
  have hc := Nat.choose_le_choose 2 hsize
  norm_num at hc
  omega

end Erdos85
