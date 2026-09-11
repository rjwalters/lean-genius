import Proofs.Erdos85DistanceLayers

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


namespace Erdos85

/-- A nonidentity adjacency-preserving map of a C4-free graph of minimum
    degree at least nine moves at least fifty-seven vertices. -/
theorem fiftySeven_le_card_moved
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (τ : V → V)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    57 ≤ Fintype.card ({v : V | τ v ≠ v} : Set V) := by
  classical
  let M : Set V := {v : V | τ v ≠ v}
  let H := G.induce M
  have hHfree : ¬ containsC4 M H := by
    rintro ⟨f, hf, hadj⟩
    apply hfree
    exact ⟨fun i => (f i).val, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  have hHmin : 8 ≤ H.minDegree := by
    have h := minDegree_sub_one_le_moved_minDegree G hfree τ hmap hmoved
    change G.minDegree - 1 ≤ H.minDegree at h
    omega
  obtain ⟨x, hx⟩ := hmoved
  let v : M := ⟨x, hx⟩
  have hdegree : 8 ≤ H.degree v := hHmin.trans (H.minDegree_le_degree v)
  have hbound := one_add_degree_add_mul_sub_two_le_card_of_minDegree H hHfree hHmin v
  norm_num only [Nat.reduceSub] at hbound
  change 57 ≤ Fintype.card M
  omega

end Erdos85

#print axioms Erdos85.fiftySeven_le_card_moved
