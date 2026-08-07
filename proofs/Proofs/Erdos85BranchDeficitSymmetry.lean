import Proofs.Erdos85CleanHighBranchObstruction

/-!
# Symmetry of branch deficits

Between two finite vertex sets, adjacency incidences can be counted from
either side.  When every vertex has at most one neighbor across, the number
of vertices missing the opposite set is therefore symmetric for equal-size
sets.  Applied to high-root branches, this makes the directed dirty-sector
miss matrix symmetric.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Bipartite adjacency incidences counted from either shore agree. -/
theorem sum_card_neighbor_inter_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) =
      ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  classical
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset] at hp ⊢
    exact ⟨hp.2.2, by simpa [G.adj_comm] using hp.2.1, hp.1⟩
  · intro p hp q hq hpq
    cases p
    cases q
    cases hpq
    rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_inter,
      SimpleGraph.mem_neighborFinset] at hp
    refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset]
      exact ⟨hp.2.2, by simpa [G.adj_comm] using hp.2.1, hp.1⟩
    · cases p
      rfl

/-- For a zero-one-valued function, its sum plus the number of zero terms is
the size of the indexing finset. -/
theorem sum_add_card_filter_eq_card_of_le_one
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (hle : ∀ x ∈ S, f x ≤ 1) :
    (∑ x ∈ S, f x) + (S.filter fun x => f x = 0).card = S.card := by
  classical
  rw [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  calc
    (∑ x ∈ S, (f x + if f x = 0 then 1 else 0)) =
        ∑ _x ∈ S, 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have := hle x hx
      by_cases hzero : f x = 0 <;> simp [hzero] <;> omega
    _ = S.card := by simp

/-- Equal-size shores with cross-degree at most one have equal numbers of
vertices with no cross-neighbor. -/
theorem card_filter_no_cross_neighbor_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcard : A.card = B.card)
    (hleA : ∀ a ∈ A, (G.neighborFinset a ∩ B).card ≤ 1)
    (hleB : ∀ b ∈ B, (G.neighborFinset b ∩ A).card ≤ 1) :
    (A.filter fun a => (G.neighborFinset a ∩ B).card = 0).card =
      (B.filter fun b => (G.neighborFinset b ∩ A).card = 0).card := by
  have hA := sum_add_card_filter_eq_card_of_le_one A
    (fun a => (G.neighborFinset a ∩ B).card) hleA
  have hB := sum_add_card_filter_eq_card_of_le_one B
    (fun b => (G.neighborFinset b ∩ A).card) hleB
  have hinc := sum_card_neighbor_inter_comm G A B
  omega

/-- The directed miss count from one high-root branch to another. -/
def highBranchMissCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s t : {z : V // z ∈ G.neighborSet v}) : ℕ :=
  ((secondLayerBranch G v s).filter fun a =>
    (G.neighborFinset a ∩ secondLayerBranch G v t).card = 0).card

/-- Equal-sized high-root branches have symmetric directed miss counts. -/
theorem highBranchMissCount_comm_of_equal_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (s t : {z : V // z ∈ G.neighborSet v})
    (hcard : (secondLayerBranch G v s).card =
      (secondLayerBranch G v t).card) :
    highBranchMissCount G v s t = highBranchMissCount G v t s := by
  apply card_filter_no_cross_neighbor_eq G
    (secondLayerBranch G v s) (secondLayerBranch G v t) hcard
  · intro a ha
    have hat : a ≠ t.1 := by
      intro hat
      subst a
      exact (Finset.mem_sdiff.mp ha).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr t.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v a t hat
  · intro b hb
    have hbs : b ≠ s.1 := by
      intro hbs
      subst b
      exact (Finset.mem_sdiff.mp hb).2 (by
        simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
        exact Or.inr s.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v b s hbs

/-- At a square-order high root all branch sizes are `d-2`, so the miss
matrix is symmetric without an extra cardinality hypothesis. -/
theorem squareOrder_highBranchMissCount_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 2 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (s t : {z : V // z ∈ G.neighborSet v}) :
    highBranchMissCount G v s t = highBranchMissCount G v t s := by
  apply highBranchMissCount_comm_of_equal_card G hfree s t
  rw [card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
      G hd hv hneigh hlocal s,
    card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
      G hd hv hneigh hlocal t]

end

end Erdos85
