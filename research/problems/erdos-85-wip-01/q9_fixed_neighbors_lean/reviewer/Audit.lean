import Proofs.Erdos85Problem

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

#print axioms Erdos85.fixed_neighbors_eq_of_moved
#print axioms Erdos85.fixed_neighborSet_subsingleton_of_moved
