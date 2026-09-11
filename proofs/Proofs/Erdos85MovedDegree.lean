import Proofs.Erdos85FixedNeighbors

namespace Erdos85

/-- Removing the fixed vertices lowers the degree of a moved vertex by at most one. -/
theorem degree_le_moved_degree_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (x : ({v : V | τ v ≠ v} : Set V)) :
    G.degree x ≤ (G.induce {v : V | τ v ≠ v}).degree x + 1 := by
  classical
  have hfixed : ((G.neighborFinset x).filter (fun u => τ u = u)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hu hv
    exact fixed_neighbors_eq_of_moved hfree τ hmap x.property hu.2 hv.2 hu.1 hv.1
  have hpart := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset x) (p := fun u => τ u = u)
  have hmove : ((G.neighborFinset x).filter (fun u => τ u ≠ u)).card =
      (G.induce {v : V | τ v ≠ v}).degree x := by
    have heq : (G.neighborFinset x).filter (fun u => τ u ≠ u) =
        G.neighborFinset x ∩ ({v : V | τ v ≠ v} : Set V).toFinset := by
      ext u
      simp
    rw [heq, ← G.map_neighborFinset_induce x, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]
  rw [hmove, G.card_neighborFinset_eq_degree] at hpart
  omega

/-- A nonempty moved induced graph has minimum degree at least the original minus one. -/
theorem minDegree_sub_one_le_moved_minDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    G.minDegree - 1 ≤ (G.induce {v : V | τ v ≠ v}).minDegree := by
  classical
  obtain ⟨x, hx⟩ := hmoved
  letI : Nonempty ({v : V | τ v ≠ v} : Set V) := ⟨⟨x, hx⟩⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  have h₁ := G.minDegree_le_degree v
  have h₂ := degree_le_moved_degree_add_one G hfree τ hmap v
  omega

end Erdos85
