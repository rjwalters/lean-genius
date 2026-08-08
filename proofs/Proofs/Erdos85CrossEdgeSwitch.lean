import Proofs.Erdos85CompensatedRepair

/-! A universal compensated switch preserving `C₄`-freeness. -/

open SimpleGraph

namespace Erdos85

def crossEdgeSwitch {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V) : SimpleGraph V :=
  deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w) ⊔ SimpleGraph.edge x w

theorem crossEdgeSwitch_adj_iff {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w a b : V) :
    (crossEdgeSwitch H x w).Adj a b ↔
      (H.Adj a b ∧ s(a,b) ∉ crossEdgeSet (H.neighborFinset x) (H.neighborFinset w)) ∨
      ((a = x ∧ b = w) ∨ (a = w ∧ b = x)) ∧ a ≠ b := by
  simp [crossEdgeSwitch, deleteCrossEdges, SimpleGraph.deleteEdges_adj, SimpleGraph.edge_adj]

set_option maxHeartbeats 800000 in
theorem crossEdgeSwitch_not_containsC4 {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    (hfree : ¬ containsC4 V H) : ¬ containsC4 V (crossEdgeSwitch H x w) := by
  rintro ⟨f, hinj, hadj⟩
  let a := f 0; let b := f 1; let c := f 2; let d := f 3
  have hab := (crossEdgeSwitch_adj_iff H x w a b).mp (hadj 0 1 (by decide))
  have hbc := (crossEdgeSwitch_adj_iff H x w b c).mp (hadj 1 2 (by decide))
  have hcd := (crossEdgeSwitch_adj_iff H x w c d).mp (hadj 2 3 (by decide))
  have hda := (crossEdgeSwitch_adj_iff H x w d a).mp (hadj 3 0 (by decide))
  have hac : a ≠ c := fun h => (by decide : (0 : Fin 4) ≠ 2) (hinj (by simpa [a,c] using h))
  have hbd : b ≠ d := fun h => (by decide : (1 : Fin 4) ≠ 3) (hinj (by simpa [b,d] using h))
  have hba : b ≠ a := fun h => (by decide : (1 : Fin 4) ≠ 0) (hinj (by simpa [a,b] using h))
  have hbcne : b ≠ c := fun h => (by decide : (1 : Fin 4) ≠ 2) (hinj (by simpa [b,c] using h))
  have hdane : d ≠ a := fun h => (by decide : (3 : Fin 4) ≠ 0) (hinj (by simpa [a,d] using h))
  have hdc : d ≠ c := fun h => (by decide : (3 : Fin 4) ≠ 2) (hinj (by simpa [c,d] using h))
  have special_eq {p q : V}
      (h : ((p = x ∧ q = w) ∨ (p = w ∧ q = x)) ∧ p ≠ q) : s(p,q) = s(x,w) := by
    rw [Sym2.eq_iff]; tauto
  have habbc : s(a,b) ≠ s(b,c) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact hba h.symm
    · exact hac h
  have habcd : s(a,b) ≠ s(c,d) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact hac h
    · exact hdane h.symm
  have habda : s(a,b) ≠ s(d,a) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨_, h⟩
    · exact hdane h.symm
    · exact hbd h
  have hbccd : s(b,c) ≠ s(c,d) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact hbcne h
    · exact hbd h
  have hbcda : s(b,c) ≠ s(d,a) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact hbd h
    · exact hba h
  have hcdda : s(c,d) ≠ s(d,a) := by
    intro h; rcases Sym2.eq_iff.mp h with ⟨h, _⟩ | ⟨h, _⟩
    · exact hdc h.symm
    · exact hac h.symm
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc <;>
    rcases hcd with hcd | hcd <;> rcases hda with hda | hda
  · exact hfree (containsC4_of_rim hab.1 hbc.1 hcd.1 hda.1 hac hbd hba hbcne hdane hdc)
  · rcases hda.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply hbc.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inr ⟨hab.1, hcd.1.symm⟩
    · apply hbc.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inl ⟨hab.1, hcd.1.symm⟩
  · rcases hcd.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply hab.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inr ⟨hda.1, hbc.1.symm⟩
    · apply hab.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inl ⟨hda.1, hbc.1.symm⟩
  · exact hcdda ((special_eq hcd).trans (special_eq hda).symm)
  · rcases hbc.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply hda.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inr ⟨hcd.1, hab.1.symm⟩
    · apply hda.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inl ⟨hcd.1, hab.1.symm⟩
  · exact hbcda ((special_eq hbc).trans (special_eq hda).symm)
  · exact hbccd ((special_eq hbc).trans (special_eq hcd).symm)
  · exact hbccd ((special_eq hbc).trans (special_eq hcd).symm)
  · rcases hab.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply hcd.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inr ⟨hbc.1, hda.1.symm⟩
    · apply hcd.2; rw [pair_mem_crossEdgeSet_iff]; simp only [SimpleGraph.mem_neighborFinset]
      exact Or.inl ⟨hbc.1, hda.1.symm⟩
  · exact habda ((special_eq hab).trans (special_eq hda).symm)
  · exact habcd ((special_eq hab).trans (special_eq hcd).symm)
  · exact habcd ((special_eq hab).trans (special_eq hcd).symm)
  · exact habbc ((special_eq hab).trans (special_eq hbc).symm)
  · exact habbc ((special_eq hab).trans (special_eq hbc).symm)
  · exact habbc ((special_eq hab).trans (special_eq hbc).symm)
  · exact habbc ((special_eq hab).trans (special_eq hbc).symm)

/-- When the switched endpoints are nonadjacent and have disjoint
neighborhoods, every vertex loses at most one edge in the cross deletion. -/
theorem crossEdgeLoss_neighborFinsets_le_one {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    (hfree : ¬ containsC4 V H) (hxw : ¬ H.Adj x w)
    (hdisj : Disjoint (H.neighborFinset x) (H.neighborFinset w)) :
    crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset w) v ≤ 1 := by
  classical
  by_cases hvx : v ∈ H.neighborFinset x
  · have hvw : v ∉ H.neighborFinset w := Finset.disjoint_left.mp hdisj hvx
    rw [crossEdgeLoss_eq_card_neighbor_inter_right H _ _ v hvx hvw]
    apply card_inter_neighborFinset_le_one hfree
    intro hv
    subst v
    exact hxw (by simpa using hvx)
  · by_cases hvw : v ∈ H.neighborFinset w
    · rw [crossEdgeLoss_eq_card_neighbor_inter_left H _ _ v hvw hvx]
      rw [Finset.inter_comm]
      apply card_inter_neighborFinset_le_one hfree
      intro hv
      subst v
      exact hxw ((by simpa using hvw : H.Adj w x).symm)
    · rw [crossEdgeLoss_eq_zero_of_not_mem H _ _ v hvx hvw]
      omega

/-- A tangent right endpoint also forces matching-like cross deletion, even
when the two neighborhoods meet: adjacent vertices to `w` have no common
neighbor with `w`, so every vertex loses at most one edge. -/
theorem crossEdgeLoss_neighborFinsets_le_one_of_tangent_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    (hfree : ¬ containsC4 V H) (hxw : ¬ H.Adj x w)
    (htangent : ∀ z, H.Adj z w →
      H.neighborFinset z ∩ H.neighborFinset w = ∅) :
    crossEdgeLoss H (H.neighborFinset x) (H.neighborFinset w) v ≤ 1 := by
  classical
  by_cases hvx : v ∈ H.neighborFinset x
  · by_cases hvw : v ∈ H.neighborFinset w
    · have hempty := htangent v ((by simpa using hvw : H.Adj w v).symm)
      have hloss : crossEdgeLoss H (H.neighborFinset x)
          (H.neighborFinset w) v =
          (H.neighborFinset v ∩ H.neighborFinset x).card := by
        rw [crossEdgeLoss]
        apply congrArg Finset.card
        ext y
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset,
          pair_mem_crossEdgeSet_iff, hvx, hvw, true_and,
          Finset.mem_inter]
        have hnot : ¬ (H.Adj v y ∧ H.Adj w y) := by
          intro h
          have hm : y ∈ H.neighborFinset v ∩ H.neighborFinset w := by
            exact Finset.mem_inter.mpr
              ⟨by simpa using h.1, by simpa using h.2⟩
          rw [hempty] at hm
          simp at hm
        tauto
      rw [hloss]
      apply card_inter_neighborFinset_le_one hfree
      intro h
      subst v
      exact H.loopless.irrefl x (by simpa using hvx)
    · rw [crossEdgeLoss_eq_card_neighbor_inter_right H _ _ v hvx hvw]
      apply card_inter_neighborFinset_le_one hfree
      intro h
      subst v
      exact hxw (by simpa using hvx)
  · by_cases hvw : v ∈ H.neighborFinset w
    · rw [crossEdgeLoss_eq_card_neighbor_inter_left H _ _ v hvw hvx]
      rw [Finset.inter_comm]
      apply card_inter_neighborFinset_le_one hfree
      intro h
      subst v
      exact hxw ((by simpa using hvw : H.Adj w x).symm)
    · rw [crossEdgeLoss_eq_zero_of_not_mem H _ _ v hvx hvw]
      omega

/-- The newly inserted edge raises the left endpoint's degree by exactly one
when it was absent from the old graph. -/
theorem crossEdgeSwitch_degree_left {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)).Adj]
    (hxw : ¬ H.Adj x w) (hne : x ≠ w) :
    (crossEdgeSwitch H x w).degree x =
      (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)).degree x + 1 := by
  classical
  let D := deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)
  have hneighbors : (crossEdgeSwitch H x w).neighborFinset x =
      insert w (D.neighborFinset x) := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    rw [crossEdgeSwitch_adj_iff]
    change _ ↔ v = w ∨ D.Adj x v
    simp only [D, deleteCrossEdges, SimpleGraph.deleteEdges_adj]
    aesop
  rw [SimpleGraph.degree, hneighbors]
  have hnot : w ∉ D.neighborFinset x := by
    rw [SimpleGraph.mem_neighborFinset]
    intro h
    exact hxw (SimpleGraph.deleteEdges_le _ h)
  rw [Finset.card_insert_of_notMem hnot,
    SimpleGraph.card_neighborFinset_eq_degree]

/-- Adding the switch edge cannot lower any degree relative to the graph after
cross-edge deletion. -/
theorem degree_deleteCrossEdges_le_crossEdgeSwitch {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)).Adj] :
    (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)).degree v ≤
      (crossEdgeSwitch H x w).degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy ⊢
  exact (show deleteCrossEdges H _ _ ≤
      deleteCrossEdges H _ _ ⊔ SimpleGraph.edge x w from le_sup_left) hy

/-- Away from its two endpoints, a cross-edge switch can only remove edges. -/
theorem crossEdgeSwitch_degree_le_of_ne_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    (hvx : v ≠ x) (hvw : v ≠ w) :
    (crossEdgeSwitch H x w).degree v ≤ H.degree v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree,
    ← SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  rw [SimpleGraph.mem_neighborFinset] at hy ⊢
  rcases (crossEdgeSwitch_adj_iff H x w v y).mp hy with hold | hnew
  · exact hold.1
  · rcases hnew.1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact (hvx h).elim
    · exact (hvw h).elim

/-- Every old vertex below the target degree must be one of the two switch
endpoints if the switched graph reaches that target. -/
theorem low_degree_vertex_is_switch_endpoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w v : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj] {d : ℕ}
    (hmin : d ≤ (crossEdgeSwitch H x w).minDegree)
    (hlow : H.degree v < d) : v = x ∨ v = w := by
  by_contra h
  push_neg at h
  have hle := crossEdgeSwitch_degree_le_of_ne_endpoints H x w v h.1 h.2
  have htarget := hmin.trans ((crossEdgeSwitch H x w).minDegree_le_degree v)
  omega

/-- A single cross-edge switch cannot repair three distinct old vertices
whose degrees are all below the target. -/
theorem crossEdgeSwitch_minDegree_lt_of_three_low_vertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    (D : Finset V) {d : ℕ} (hD : 3 ≤ D.card)
    (hlow : ∀ v ∈ D, H.degree v < d) :
    (crossEdgeSwitch H x w).minDegree < d := by
  by_contra h
  have hmin : d ≤ (crossEdgeSwitch H x w).minDegree := by omega
  have hsub : D ⊆ {x,w} := by
    intro v hv
    have hend := low_degree_vertex_is_switch_endpoint H x w v hmin (hlow v hv)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hend
  have hc := Finset.card_le_card hsub
  have hp : ({x,w} : Finset V).card ≤ 2 :=
    (Finset.card_insert_le x {w}).trans_eq (by simp)
  omega

/-- Abstract completion theorem for the compensated switch: after the cross
deletion, a unique one-unit defect at `x` is repaired by the edge `xw`. -/
theorem crossEdgeSwitch_minDegree_of_unique_defect {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)).Adj]
    (d : ℕ) (hxw : ¬ H.Adj x w) (hne : x ≠ w)
    (hx : (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).degree x = d - 1)
    (hother : ∀ v ≠ x, d ≤ (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).degree v) :
    d ≤ (crossEdgeSwitch H x w).minDegree := by
  letI : Nonempty V := ⟨x⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  by_cases hv : v = x
  · subst v
    rw [crossEdgeSwitch_degree_left H x w hxw hne, hx]
    omega
  · exact (hother v hv).trans
      (degree_deleteCrossEdges_le_crossEdgeSwitch H x w v)

/-- Witness-level form of the unique-defect switch theorem.  This is the
final abstract assembly interface used by finite-geometry constructions. -/
theorem c4FreeMinDegreeWitness_crossEdgeSwitch_of_unique_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)).Adj]
    {n d : ℕ} (hcard : Fintype.card V = n)
    (hfree : ¬ containsC4 V H) (hxw : ¬ H.Adj x w) (hne : x ≠ w)
    (hx : (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).degree x = d - 1)
    (hother : ∀ v ≠ x, d ≤ (deleteCrossEdges H (H.neighborFinset x)
      (H.neighborFinset w)).degree v) :
    C4FreeMinDegreeWitness n d := by
  apply c4FreeMinDegreeWitness_of_card_eq (crossEdgeSwitch H x w) hcard
  · exact crossEdgeSwitch_minDegree_of_unique_defect H x w d hxw hne hx hother
  · exact crossEdgeSwitch_not_containsC4 H x w hfree

/-- Reusable tangent-switch criterion in terms of the old graph.  The defect
has degree `d-1`, every other vertex starts at degree at least `d`, and every
vertex actually touched by cross deletion has one additional unit of slack. -/
theorem c4FreeMinDegreeWitness_tangentSwitch_of_slack
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x w : V)
    [DecidableRel (crossEdgeSwitch H x w).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset w)).Adj]
    {n d : ℕ} (hcard : Fintype.card V = n)
    (hfree : ¬ containsC4 V H) (hxw : ¬ H.Adj x w) (hne : x ≠ w)
    (htangent : ∀ z, H.Adj z w →
      H.neighborFinset z ∩ H.neighborFinset w = ∅)
    (hx : H.degree x = d - 1)
    (hbase : ∀ v ≠ x, d ≤ H.degree v)
    (hslack : ∀ v, 1 ≤ crossEdgeLoss H (H.neighborFinset x)
      (H.neighborFinset w) v → d + 1 ≤ H.degree v) :
    C4FreeMinDegreeWitness n d := by
  apply c4FreeMinDegreeWitness_crossEdgeSwitch_of_unique_defect
    H x w hcard hfree hxw hne
  · have hxS : x ∉ H.neighborFinset x := by simp
    have hxT : x ∉ H.neighborFinset w := by
      rw [SimpleGraph.mem_neighborFinset]
      exact fun h => hxw h.symm
    have hloss := crossEdgeLoss_eq_zero_of_not_mem H
      (H.neighborFinset x) (H.neighborFinset w) x hxS hxT
    have hsplit := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset w) x
    omega
  · intro v hvx
    have hlossle := crossEdgeLoss_neighborFinsets_le_one_of_tangent_right
      H x w v hfree hxw htangent
    have hsplit := degree_deleteCrossEdges_add_loss H
      (H.neighborFinset x) (H.neighborFinset w) v
    by_cases hz : crossEdgeLoss H (H.neighborFinset x)
        (H.neighborFinset w) v = 0
    · have := hbase v hvx
      omega
    · have hp : 1 ≤ crossEdgeLoss H (H.neighborFinset x)
          (H.neighborFinset w) v := Nat.one_le_iff_ne_zero.mpr hz
      have := hslack v hp
      omega

theorem crossEdgeSwitch_comm {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) :
    crossEdgeSwitch H x y = crossEdgeSwitch H y x := by
  ext a b
  rw [crossEdgeSwitch_adj_iff, crossEdgeSwitch_adj_iff]
  simp only [pair_mem_crossEdgeSet_iff, SimpleGraph.mem_neighborFinset]
  tauto

theorem crossEdgeSwitch_degree_right {V : Type*} [Fintype V]
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V)
    [DecidableRel (crossEdgeSwitch H x y).Adj]
    [DecidableRel (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)).Adj]
    (hxy : ¬ H.Adj x y) (hne : x ≠ y) :
    (crossEdgeSwitch H x y).degree y =
      (deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)).degree y + 1 := by
  classical
  let D := deleteCrossEdges H (H.neighborFinset x) (H.neighborFinset y)
  have hneighbors : (crossEdgeSwitch H x y).neighborFinset y =
      insert x (D.neighborFinset y) := by
    ext v
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert]
    rw [crossEdgeSwitch_adj_iff]
    change _ ↔ v = x ∨ D.Adj y v
    simp only [D, deleteCrossEdges, SimpleGraph.deleteEdges_adj]
    aesop
  rw [SimpleGraph.degree, hneighbors]
  have hnot : x ∉ D.neighborFinset y := by
    rw [SimpleGraph.mem_neighborFinset]
    intro h
    exact hxy ((SimpleGraph.deleteEdges_le _ h).symm)
  rw [Finset.card_insert_of_notMem hnot,
    SimpleGraph.card_neighborFinset_eq_degree]

end Erdos85
