import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Ordinary-neighbor coverage for residual full centers

This isolates the set-theoretic geometry used in the Baer residual-center
argument.  A residual center's neighbors stay inside the placement, every
non-ordinary placed point is a center, and residual centers avoid all other
centers; hence every neighbor is ordinary.
-/

open SimpleGraph

namespace Erdos85

/-- Pointwise residual-full-center coverage. -/
theorem neighborFinset_subset_ordinary_of_inside_avoid_centers
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (S X F : Finset V) (g : V)
    (hinside : A.neighborFinset g ⊆ S)
    (hnonordinary : S \ X ⊆ F)
    (havoid : Disjoint (A.neighborFinset g) F) :
    A.neighborFinset g ⊆ X := by
  intro u hu
  by_contra huX
  have huS : u ∈ S := hinside hu
  have huF : u ∈ F := hnonordinary (Finset.mem_sdiff.mpr ⟨huS, huX⟩)
  exact (Finset.disjoint_left.mp havoid hu huF)

/-- Block form for the full residual-center set `R`. -/
theorem residualCenter_neighborFinset_subset_ordinary
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (R S X F : Finset V)
    (hinside : ∀ g ∈ R, A.neighborFinset g ⊆ S)
    (hnonordinary : S \ X ⊆ F)
    (havoid : ∀ g ∈ R, Disjoint (A.neighborFinset g) F) :
    ∀ g ∈ R, A.neighborFinset g ⊆ X := by
  intro g hg
  exact neighborFinset_subset_ordinary_of_inside_avoid_centers
    A S X F g (hinside g hg) hnonordinary (havoid g hg)

end Erdos85

#print axioms Erdos85.neighborFinset_subset_ordinary_of_inside_avoid_centers
#print axioms Erdos85.residualCenter_neighborFinset_subset_ordinary
