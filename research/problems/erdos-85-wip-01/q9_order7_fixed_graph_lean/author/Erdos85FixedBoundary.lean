import Proofs.Erdos85FixedNeighbors
import Proofs.Erdos85GadgetCounting

namespace Erdos85

/-- Boundary counting for the fixed set of an adjacency-preserving map in a
regular C4-free graph. Each moved vertex has at most one fixed neighbour. -/
theorem fixed_degree_sum_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hreg : ∀ v, G.degree v = d)
    (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y)) :
    (d + 1) * Fintype.card ({v : V | τ v = v} : Set V) ≤
      (∑ v : ({v : V | τ v = v} : Set V),
        (G.induce {v : V | τ v = v}).degree v) + Fintype.card V := by
  classical
  let F : Set V := {v : V | τ v = v}
  let b : V → ℕ := fun v => (G.neighborFinset v ∩ F.toFinset).card
  have htotal : (∑ v : V, b v) = d * Fintype.card F := by
    have h := sum_card_neighbor_inter_eq_sum_degree G F.toFinset
    change (∑ v : V, b v) = _ at h
    simpa [hreg, Nat.mul_comm] using h
  have hinside : ∀ v : F, b v = (G.induce F).degree v := by
    intro v
    dsimp [b]
    rw [← G.map_neighborFinset_induce v, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]
  have houtside : ∀ v : (Fᶜ : Set V), b v ≤ 1 := by
    intro v
    apply Finset.card_le_one.mpr
    intro u hu w hw
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      Set.mem_toFinset] at hu hw
    exact fixed_neighbors_eq_of_moved hfree τ hmap v.property hu.2 hw.2 hu.1 hw.1
  have hsumoutside : (∑ v : (Fᶜ : Set V), b v) ≤ Fintype.card (Fᶜ : Set V) := by
    calc
      (∑ v : (Fᶜ : Set V), b v) ≤ ∑ _v : (Fᶜ : Set V), 1 := Finset.sum_le_sum (fun v _ => houtside v)
      _ = Fintype.card (Fᶜ : Set V) := by simp
  have hsplit := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ F) b
  have hcard := Fintype.sum_subtype_add_sum_subtype (fun v => v ∈ F) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hcard
  simp only [hinside] at hsplit
  rw [htotal] at hsplit
  change Fintype.card F + Fintype.card (Fᶜ : Set V) = Fintype.card V at hcard
  change (∑ v : F, (G.induce F).degree v) +
    (∑ v : (Fᶜ : Set V), b v) = d * Fintype.card F at hsplit
  change (d + 1) * Fintype.card F ≤ (∑ v : F, (G.induce F).degree v) + Fintype.card V
  nlinarith

end Erdos85
