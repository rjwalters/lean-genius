import Proofs.Erdos85MovedDegree
import Proofs.Erdos85DistanceLayers

/-!
# Regularity of a small moved-vertex graph

Below 64 moved vertices, minimum degree eight forces the moved induced graph
to be eight-regular. If the original graph is nine-regular, every moved vertex
therefore has exactly one fixed neighbour. This provides the exact boundary
count used when an order-three action moves 60 or 63 vertices.
-/

namespace Erdos85

/-- A moved induced graph of order below 64 is eight-regular. -/
theorem moved_degree_eq_eight_of_card_lt_sixtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hcard : Fintype.card ({v : V | τ v ≠ v} : Set V) < 64)
    (x : ({v : V | τ v ≠ v} : Set V)) :
    (G.induce {v : V | τ v ≠ v}).degree x = 8 := by
  classical
  let M : Set V := {v : V | τ v ≠ v}
  let H := G.induce M
  have hHfree : ¬ containsC4 M H := by
    rintro ⟨f, hf, hadj⟩
    exact hfree ⟨fun i => (f i).val, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  have hHmin : 8 ≤ H.minDegree := by
    have h := minDegree_sub_one_le_moved_minDegree G hfree τ hmap ⟨x, x.property⟩
    change G.minDegree - 1 ≤ H.minDegree at h
    omega
  exact regular_of_minDegree_card_lt_nextMooreLayer H hHfree (by norm_num) hHmin
    (by change Fintype.card M < 64; exact hcard) x

/-- In the nine-regular case, each moved vertex has exactly one fixed neighbour. -/
theorem card_fixed_neighbors_eq_one_of_moved_card_lt_sixtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hreg : ∀ v, G.degree v = 9)
    (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hcard : Fintype.card ({v : V | τ v ≠ v} : Set V) < 64)
    (x : ({v : V | τ v ≠ v} : Set V)) :
    ((G.neighborFinset x).filter (fun u => τ u = u)).card = 1 := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := G.neighborFinset x) (p := fun u => τ u = u)
  have hmove : ((G.neighborFinset x).filter (fun u => τ u ≠ u)).card = 8 := by
    have heq : (G.neighborFinset x).filter (fun u => τ u ≠ u) =
        G.neighborFinset x ∩ ({v : V | τ v ≠ v} : Set V).toFinset := by
      ext u
      simp
    rw [heq, ← G.map_neighborFinset_induce x, Finset.card_map,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact moved_degree_eq_eight_of_card_lt_sixtyFour G hfree hmin τ hmap hcard x
  rw [hmove, G.card_neighborFinset_eq_degree, hreg] at hpart
  omega

end Erdos85
