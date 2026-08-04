import Proofs.Erdos85CrossEdgeSwitchProgram

/-! Defect propagation and repair cascades in finite switch programs. -/

open SimpleGraph

namespace Erdos85

theorem canonicalCrossEdgeSwitch_eq_crossEdgeSwitch
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V) :
    canonicalCrossEdgeSwitch H x w = crossEdgeSwitch H x w := by
  classical
  ext a b
  unfold canonicalCrossEdgeSwitch
  rw [crossEdgeSwitch_adj_iff, crossEdgeSwitch_adj_iff]
  simp only [pair_mem_crossEdgeSet_iff, SimpleGraph.mem_neighborFinset]

/-- Away from the inserted edge's endpoints, the switched graph has exactly
the degree left by the cross deletion. -/
theorem crossEdgeSwitch_degree_eq_deleteCrossEdges_of_ne_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    (hvx : v ≠ x) (hvw : v ≠ w) :
    (crossEdgeSwitch H x w).degree v =
      (deleteCrossEdges H (H.neighborFinset x)
        (H.neighborFinset w)).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply congrArg Finset.card
  ext y
  simp only [SimpleGraph.mem_neighborFinset]
  rw [crossEdgeSwitch_adj_iff]
  simp only [deleteCrossEdges, SimpleGraph.deleteEdges_adj]
  constructor
  · rintro (hold | hnew)
    · exact hold
    · rcases hnew.1 with ⟨h, _⟩ | ⟨h, _⟩
      · exact (hvx h).elim
      · exact (hvw h).elim
  · exact Or.inl

/-- Deleting even one incident cross edge at an untouched target-tight vertex
turns it into a strict defect. -/
theorem crossEdgeSwitch_degree_lt_of_tight_of_positive_loss
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    {d : ℕ} (hdeg : H.degree v = d)
    (hvx : v ≠ x) (hvw : v ≠ w)
    (hloss : 1 ≤ crossEdgeLoss H (H.neighborFinset x)
      (H.neighborFinset w) v) :
    (crossEdgeSwitch H x w).degree v < d := by
  have hsplit := degree_deleteCrossEdges_add_loss H
    (H.neighborFinset x) (H.neighborFinset w) v
  rw [crossEdgeSwitch_degree_eq_deleteCrossEdges_of_ne_endpoints
    H x w v hvx hvw]
  omega

/-- A target-tight vertex damaged at one stage must occur as an endpoint in
the remaining program if the final graph recovers the target everywhere. -/
theorem positive_loss_forces_later_switch_endpoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    (P : List (V × V)) {d : ℕ} (hdeg : H.degree v = d)
    (hvx : v ≠ x) (hvw : v ≠ w)
    (hloss : 1 ≤ crossEdgeLoss H (H.neighborFinset x)
      (H.neighborFinset w) v)
    (hfinal : ∀ u, d ≤ canonicalDegree
      (crossEdgeSwitchProgram (canonicalCrossEdgeSwitch H x w) P) u) :
    v ∈ crossEdgeSwitchProgramEndpoints P := by
  apply low_degree_vertex_mem_crossEdgeSwitchProgramEndpoints
    (canonicalCrossEdgeSwitch H x w) P v hfinal
  have hlt := crossEdgeSwitch_degree_lt_of_tight_of_positive_loss
    H x w v hdeg hvx hvw hloss
  have heq : canonicalDegree (canonicalCrossEdgeSwitch H x w) v =
      (crossEdgeSwitch H x w).degree v := by
    classical
    rw [canonicalCrossEdgeSwitch_eq_crossEdgeSwitch H x w]
    unfold canonicalDegree
    rw [Set.ncard_eq_toFinset_card']
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply congrArg Finset.card
    ext y
    simp only [Set.mem_toFinset, SimpleGraph.mem_neighborSet,
      SimpleGraph.mem_neighborFinset]
  rw [heq]
  exact hlt

end Erdos85

