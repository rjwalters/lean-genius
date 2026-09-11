import Proofs.Erdos85AttachedPrimeOrbit
import Proofs.Erdos85FixedNeighbors

namespace Erdos85

/-- The moved neighbours attached to a given vertex. -/
def movedNeighborFinset {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (τ : V → V) (u : V) : Finset V :=
  (G.neighborFinset u).filter (fun x => τ x ≠ x)

@[simp] theorem mem_movedNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (τ : V → V) (u x : V) :
    x ∈ movedNeighborFinset G τ u ↔ G.Adj u x ∧ τ x ≠ x := by
  simp [movedNeighborFinset]

/-- Attached sets of distinct fixed vertices are disjoint. -/
theorem movedNeighborFinset_disjoint_of_fixed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    {u v : V} (hu : τ u = u) (hv : τ v = v) (huv : u ≠ v) :
    Disjoint (movedNeighborFinset G τ u) (movedNeighborFinset G τ v) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rw [mem_movedNeighborFinset] at hx hy
  exact huv (fixed_neighbors_eq_of_moved hfree τ hmap hx.2 hu hv hx.1.symm hy.1.symm)

/-- Adjacent fixed centres have no edges between their attached sets. -/
theorem not_adj_movedNeighborFinset_of_fixed_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V)
    {u v x y : V} (hu : τ u = u) (hv : τ v = v) (huv : G.Adj u v)
    (hx : x ∈ movedNeighborFinset G τ u) (hy : y ∈ movedNeighborFinset G τ v) :
    ¬ G.Adj x y := by
  rw [mem_movedNeighborFinset] at hx hy
  intro hxy
  have huy : u ≠ y := by intro h; subst y; exact hy.2 hu
  have hvx : v ≠ x := by intro h; subst x; exact hx.2 hv
  exact hfree (containsC4_of_two_common huy hvx huv.symm hy.1 hx.1.symm hxy)

/-- Any vertex other than a centre meets its attached set at most once. -/
theorem card_neighbor_inter_movedNeighborFinset_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (τ : V → V) {u x : V} (hxu : x ≠ u) :
    (G.neighborFinset x ∩ movedNeighborFinset G τ u).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, mem_movedNeighborFinset] at ha hb
  by_contra hab
  exact hfree (containsC4_of_two_common hxu hab ha.1.symm ha.2.1.symm hb.1.symm hb.2.1.symm)

/-- Cardinal form of the seven attached neighbours. -/
theorem card_movedNeighborFinset_eq_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (τ : V → V) (u : V) (hu : τ u = u) (hdegree : G.degree u = 9)
    (hfixed : (G.induce {v : V | τ v = v}).degree ⟨u, hu⟩ = 2) :
    (movedNeighborFinset G τ u).card = 7 := by
  classical
  have h := card_moved_neighbors_eq_seven_of_degree_nine_fixed_two G τ u hu hdegree hfixed
  have heq : movedNeighborFinset G τ u =
      ({x : V | G.Adj u x ∧ τ x ≠ x} : Set V).toFinset := by ext x; simp
  rw [heq, Set.toFinset_card]
  exact h

end Erdos85
