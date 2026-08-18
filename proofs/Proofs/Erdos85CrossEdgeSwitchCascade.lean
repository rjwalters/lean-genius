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

/-- More generally, an untouched vertex becomes a strict defect whenever its
cross-edge loss exceeds its available slack above the target. -/
theorem crossEdgeSwitch_degree_lt_of_loss_exceeds_slack
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    {d : ℕ} (hvx : v ≠ x) (hvw : v ≠ w)
    (hexcess : H.degree v < d + crossEdgeLoss H (H.neighborFinset x)
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

/-- Any vertex whose loss exceeds its slack must be named by a successful
continuation of the switch program. -/
theorem excess_loss_forces_later_switch_endpoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    (P : List (V × V)) {d : ℕ} (hvx : v ≠ x) (hvw : v ≠ w)
    (hexcess : H.degree v < d + crossEdgeLoss H (H.neighborFinset x)
      (H.neighborFinset w) v)
    (hfinal : ∀ u, d ≤ canonicalDegree
      (crossEdgeSwitchProgram (canonicalCrossEdgeSwitch H x w) P) u) :
    v ∈ crossEdgeSwitchProgramEndpoints P := by
  apply low_degree_vertex_mem_crossEdgeSwitchProgramEndpoints
    (canonicalCrossEdgeSwitch H x w) P v hfinal
  have hlt := crossEdgeSwitch_degree_lt_of_loss_exceeds_slack
    H x w v hvx hvw hexcess
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

/-- In a successful final switch, every target-tight vertex with positive
cross-edge loss must itself be one of the two switch endpoints. -/
theorem tight_positive_loss_is_endpoint_of_successful_crossEdgeSwitch
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    {d : ℕ} (hfinal : ∀ u, d ≤ (crossEdgeSwitch H x w).degree u)
    (hdeg : H.degree v = d)
    (hloss : 1 ≤ crossEdgeLoss H (H.neighborFinset x)
      (H.neighborFinset w) v) :
    v = x ∨ v = w := by
  by_contra h
  push_neg at h
  have hlt := crossEdgeSwitch_degree_lt_of_tight_of_positive_loss
    H x w v hdeg h.1 h.2 hloss
  have := hfinal v
  omega

/-- Equivalently, away from the two endpoints a successful final switch must
have zero loss at every target-tight old vertex. -/
theorem crossEdgeLoss_eq_zero_of_tight_of_successful_crossEdgeSwitch
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    {d : ℕ} (hfinal : ∀ u, d ≤ (crossEdgeSwitch H x w).degree u)
    (hdeg : H.degree v = d) (hvx : v ≠ x) (hvw : v ≠ w) :
    crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset w) v = 0 := by
  by_contra h
  have hp := Nat.one_le_iff_ne_zero.mpr h
  rcases tight_positive_loss_is_endpoint_of_successful_crossEdgeSwitch
    H x w v hfinal hdeg hp with rfl | rfl
  · exact hvx rfl
  · exact hvw rfl

/-- If the proposed switch endpoints are already adjacent, the switch is a
subgraph of the old graph: its nominal inserted edge was already present. -/
theorem crossEdgeSwitch_le_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V) (hxw : H.Adj x w) :
    crossEdgeSwitch H x w ≤ H := by
  intro a b h
  rw [crossEdgeSwitch_adj_iff] at h
  rcases h with h | h
  · exact h.1
  · rcases h.1 with h | h
    · simpa [h.1, h.2] using hxw
    · simpa [h.1, h.2] using hxw.symm

theorem crossEdgeSwitch_degree_le_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj] (hxw : H.Adj x w) :
    (crossEdgeSwitch H x w).degree v ≤ H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy ⊢
  exact crossEdgeSwitch_le_of_adj H x w hxw hy

/-- A switch which repairs a strict defect must join it to a nonneighbor. -/
theorem successful_crossEdgeSwitch_not_adjacent_at_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    {d : ℕ} (hdefect : H.degree x < d)
    (hfinal : d ≤ (crossEdgeSwitch H x w).degree x) : ¬ H.Adj x w := by
  intro hxw
  have hle := crossEdgeSwitch_degree_le_of_adj H x w x hxw
  omega

/-- A switch with two equal endpoints inserts no edge and is a subgraph. -/
theorem crossEdgeSwitch_le_of_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V) (hxw : x = w) :
    crossEdgeSwitch H x w ≤ H := by
  subst w
  intro a b h
  rw [crossEdgeSwitch_adj_iff] at h
  rcases h with h | h
  · exact h.1
  · rcases h with ⟨hnew, hne⟩
    rcases hnew with ⟨hax, hbx⟩ | ⟨hax, hbx⟩
    · exact (hne (hax.trans hbx.symm)).elim
    · exact (hne (hax.trans hbx.symm)).elim

/-- A switch which repairs a strict defect has two distinct endpoints. -/
theorem successful_crossEdgeSwitch_ne_at_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    {d : ℕ} (hdefect : H.degree x < d)
    (hfinal : d ≤ (crossEdgeSwitch H x w).degree x) : x ≠ w := by
  intro hxw
  have hle : (crossEdgeSwitch H x w).degree x ≤ H.degree x := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree,
      ← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy ⊢
    exact crossEdgeSwitch_le_of_eq H x w hxw hy
  omega

/-- Repairing a vertex which is exactly one below target uses the entire
one-edge gain: no incident cross edge at that defect may be deleted. -/
theorem crossEdgeLoss_eq_zero_at_repaired_one_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    {d : ℕ} (hpos : 0 < d) (hdefect : H.degree x = d - 1)
    (hfinal : d ≤ (crossEdgeSwitch H x w).degree x) :
    crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset w) x = 0 := by
  have hlt : H.degree x < d := by omega
  have hne := successful_crossEdgeSwitch_ne_at_defect H x w hlt hfinal
  have hadj := successful_crossEdgeSwitch_not_adjacent_at_defect H x w hlt hfinal
  have hs := degree_deleteCrossEdges_add_loss H
    (H.neighborFinset x) (H.neighborFinset w) x
  have hleft := crossEdgeSwitch_degree_left H x w hadj hne
  omega

/-- Complete local certificate required of a switch repairing a one-unit
defect. -/
theorem successful_crossEdgeSwitch_one_defect_constraints
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).Adj]
    {d : ℕ} (hpos : 0 < d) (hdefect : H.degree x = d - 1)
    (hfinal : d ≤ (crossEdgeSwitch H x w).degree x) :
    x ≠ w ∧ ¬ H.Adj x w ∧
      crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset w) x = 0 := by
  have hlt : H.degree x < d := by omega
  exact ⟨successful_crossEdgeSwitch_ne_at_defect H x w hlt hfinal,
    successful_crossEdgeSwitch_not_adjacent_at_defect H x w hlt hfinal,
    crossEdgeLoss_eq_zero_at_repaired_one_defect H x w hpos hdefect hfinal⟩

/-- A common neighbor of `v` and the right switch endpoint selects an
incident cross edge at every neighbor `v` of the left endpoint. -/
theorem one_le_crossEdgeLoss_neighborFinsets_of_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v t : V)
    (hxv : H.Adj x v) (hvt : H.Adj v t) (hwt : H.Adj w t) :
    1 ≤ crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset w) v := by
  apply one_le_crossEdgeLoss_of_adj_of_mem H
  · exact hvt
  · simpa only [SimpleGraph.mem_neighborFinset] using hxv
  · simpa only [SimpleGraph.mem_neighborFinset] using hwt

/-- An old edge survives a cross-edge switch whenever one of its endpoints
lies in neither switch neighborhood. -/
theorem crossEdgeSwitch_adj_of_adj_of_endpoint_outside
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w p q : V)
    (hpq : H.Adj p q) (hxp : ¬ H.Adj x p) (hwp : ¬ H.Adj w p) :
    (crossEdgeSwitch H x w).Adj p q := by
  rw [crossEdgeSwitch_adj_iff]
  left
  refine ⟨hpq, ?_⟩
  rw [pair_mem_crossEdgeSet_iff]
  simp only [SimpleGraph.mem_neighborFinset]
  push Not
  exact ⟨fun hp => (hxp hp).elim, fun hp => (hwp hp).elim⟩

end Erdos85
