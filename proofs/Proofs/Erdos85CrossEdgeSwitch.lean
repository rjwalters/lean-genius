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

end Erdos85
