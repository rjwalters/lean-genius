import Proofs.Erdos85Problem
import Proofs.Erdos85GadgetCounting


/-!
# Fixed neighbours of a moved vertex

In a C4-free graph, a vertex moved by an adjacency-preserving map has at
most one fixed neighbour. No bijectivity or finite-order hypothesis is needed.
This supplies the boundary bound in prime-order fixed-point arguments.
-/

namespace Erdos85

/-- Two fixed neighbours of a moved vertex coincide. -/
theorem fixed_neighbors_eq_of_moved {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    {x u v : V} (hx : τ x ≠ x)
    (hu : τ u = u) (hv : τ v = v)
    (hxu : G.Adj x u) (hxv : G.Adj x v) : u = v := by
  by_contra huv
  have hτxu : G.Adj (τ x) u := by simpa only [hu] using hmap hxu
  have hτxv : G.Adj (τ x) v := by simpa only [hv] using hmap hxv
  exact hfree (containsC4_of_two_common huv (Ne.symm hx)
    hxu hxv hτxu hτxv)

/-- The fixed neighbours of a moved vertex form a subsingleton set. -/
theorem fixed_neighborSet_subsingleton_of_moved {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    {x : V} (hx : τ x ≠ x) :
    Set.Subsingleton {u : V | G.Adj x u ∧ τ u = u} := by
  intro u hu v hv
  exact fixed_neighbors_eq_of_moved hfree τ hmap hx hu.2 hv.2 hu.1 hv.1

end Erdos85


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
#print axioms Erdos85.fixed_degree_sum_boundary
