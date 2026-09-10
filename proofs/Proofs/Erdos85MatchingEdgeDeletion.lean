import Proofs.Erdos85OrderFortyNineThreeHighTripleFarEdgeDecomposition

/-! Structural deletion of an isolated matching edge. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem matching_edge_neighbor_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x ≤ 1) {a b : V} (hab : G.Adj a b) (x : V) :
    G.Adj a x ↔ x = b := by
  constructor
  · intro hax
    have hc : (G.neighborFinset a).card ≤ 1 := by simpa using hdegree a
    exact Finset.card_le_one.mp hc x ((G.mem_neighborFinset a x).mpr hax)
      b ((G.mem_neighborFinset a b).mpr hab)
  · rintro rfl
    exact hab

theorem matching_edge_deletion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x ≤ 1) {a b : V} (hab : G.Adj a b) :
    let R := Finset.univ \ ({a,b} : Finset V)
    R.card + 2 = Fintype.card V ∧
      (G.induce (↑R : Set V)).edgeFinset.card + 1 = G.edgeFinset.card ∧
      (∀ x : (↑R : Set V), (G.induce (↑R : Set V)).degree x ≤ 1) ∧
      (∀ x ∈ R, ¬ G.Adj a x ∧ ¬ G.Adj b x) := by
  classical
  let R := Finset.univ \ ({a,b} : Finset V)
  change R.card + 2 = Fintype.card V ∧
    (G.induce (↑R : Set V)).edgeFinset.card + 1 = G.edgeFinset.card ∧
    (∀ x : (↑R : Set V), (G.induce (↑R : Set V)).degree x ≤ 1) ∧
    (∀ x ∈ R, ¬ G.Adj a x ∧ ¬ G.Adj b x)
  have habne := hab.ne
  have haR : a ∉ R := by simp [R]
  have hbR : b ∉ R := by simp [R]
  have hno (x : V) (hx : x ∈ R) : ¬ G.Adj a x ∧ ¬ G.Adj b x := by
    constructor
    · intro hax
      have he := (matching_edge_neighbor_iff G hdegree hab x).mp hax
      exact hbR (he ▸ hx)
    · intro hbx
      have he := (matching_edge_neighbor_iff G hdegree hab.symm x).mp hbx
      exact haR (he ▸ hx)
  have ha0 : (G.neighborFinset a ∩ R).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hno x (Finset.mem_inter.mp hx).2).1
      ((G.mem_neighborFinset a x).mp (Finset.mem_inter.mp hx).1)
  have hb0 : (G.neighborFinset b ∩ R).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hno x (Finset.mem_inter.mp hx).2).2
      ((G.mem_neighborFinset b x).mp (Finset.mem_inter.mp hx).1)
  have hins : insert a (insert b R) = Finset.univ := by
    ext x
    simp only [R, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton]
    tauto
  have hpair : ({a,b} : Finset V).card = 2 := by simp [habne]
  have hcardR : R.card + 2 = Fintype.card V := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({a,b} : Finset V))
    simpa only [R, hpair, Finset.card_univ] using hc
  have he := induced_edges_insert_two_vertices G R a b haR hbR habne
  rw [hins, ha0, hb0, if_pos hab, Nat.add_zero, Nat.add_zero] at he
  have hu : (G.induce (↑(Finset.univ : Finset V) : Set V)).edgeFinset.card = G.edgeFinset.card := by
    have hh := sum_internalNeighbor_card_eq_twice_induced_edges G (Finset.univ : Finset V)
    simp only [Finset.filter_mem_eq_inter, Finset.inter_univ, SimpleGraph.card_neighborFinset_eq_degree] at hh
    have hg := SimpleGraph.sum_degrees_eq_twice_card_edges G
    omega
  rw [hu] at he
  refine ⟨hcardR, he.symm, ?_, hno⟩
  intro x
  rw [degree_induce_finset_eq_card_inter]
  exact (Finset.card_le_card Finset.inter_subset_left).trans (by simpa using hdegree x.val)

end
end Erdos85
#print axioms Erdos85.matching_edge_neighbor_iff
#print axioms Erdos85.matching_edge_deletion
