import Proofs.Erdos85Problem

/-!
# Free involutions in C₄-free graphs

An adjacency-preserving involution carries a common neighbour of `u` and `τ u`
to another common neighbour. If `u` is moved, C₄-freeness forces that neighbour
to be fixed. Thus a fixed-point-free involution leaves no common neighbours
between a vertex and its image. This supplies the missing antipodal two-step
offset used in the even-order cyclic-action restrictions for Erdős problem 85.
-/

namespace Erdos85

/-- A common neighbour of a moved involution pair must be fixed. -/
theorem involution_common_neighbor_fixed {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hinv : Function.Involutive τ)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    {u v : V} (hu : τ u ≠ u) (huv : G.Adj u v)
    (hτuv : G.Adj (τ u) v) : τ v = v := by
  by_contra hv
  have h₁ : G.Adj (τ v) u := by
    simpa only [hinv u] using (hmap hτuv).symm
  have h₂ : G.Adj (τ v) (τ u) := (hmap huv).symm
  exact hfree (containsC4_of_two_common (Ne.symm hu) (Ne.symm hv)
    huv.symm hτuv.symm h₁ h₂)

/-- A free involution pair has no common neighbour in a C₄-free graph. -/
theorem free_involution_no_common_neighbor {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hinv : Function.Involutive τ)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hfix : ∀ x, τ x ≠ x) (u v : V) :
    ¬ (G.Adj u v ∧ G.Adj (τ u) v) := by
  rintro ⟨huv, hτuv⟩
  exact hfix v (involution_common_neighbor_fixed hfree τ hinv hmap
    (hfix u) huv hτuv)

/-- The neighbour sets of a free involution pair are disjoint. -/
theorem free_involution_disjoint_neighborSet {V : Type*} {G : SimpleGraph V}
    (hfree : ¬ containsC4 V G) (τ : V → V)
    (hinv : Function.Involutive τ)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hfix : ∀ x, τ x ≠ x) (u : V) :
    Disjoint (G.neighborSet u) (G.neighborSet (τ u)) := by
  rw [Set.disjoint_left]
  intro v huv hτuv
  exact free_involution_no_common_neighbor hfree τ hinv hmap hfix u v ⟨huv, hτuv⟩

end Erdos85

#print axioms Erdos85.involution_common_neighbor_fixed
#print axioms Erdos85.free_involution_no_common_neighbor
#print axioms Erdos85.free_involution_disjoint_neighborSet
