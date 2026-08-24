import Proofs.Erdos85ThreeSeparatorComplementaryPFiberPacking

/-!
# Uniform Y-side wing-fiber sizes

For centers adjacent to a separator point, the Y-shore profile reduces to
`|N_A(z)∩Y| + 1_R(z) = b` (the exceptional `+1_c` term vanishes because
`c` is not adjacent to W).  Hence K-wing centers outside R have b-point
fibers, while R-wing and incident-P centers have `(b-1)`-point fibers.
This is the local size statement (B43).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact dichotomy supplied by the Y-side indicator profile. -/
theorem uniform_Y_fiber_card_eq_of_indicator_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (Y R : Finset V) (b : ℕ)
    (hprofile : ∀ z,
      (A.neighborFinset z ∩ Y).card + (if z ∈ R then 1 else 0) = b) :
    (∀ z ∉ R, (A.neighborFinset z ∩ Y).card = b) ∧
      ∀ z ∈ R, (A.neighborFinset z ∩ Y).card = b - 1 := by
  constructor
  · intro z hzR
    have hp := hprofile z
    simpa [hzR] using hp
  · intro z hzR
    have hp := hprofile z
    simp [hzR] at hp
    omega

/-- B43 packaged for the three kinds of centers in a fixed wing. -/
theorem uniform_Y_wing_fiber_sizes
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (Y R KW RW PW : Finset V) (b : ℕ)
    (hprofile : ∀ z,
      (A.neighborFinset z ∩ Y).card + (if z ∈ R then 1 else 0) = b)
    (hKWR : Disjoint KW R)
    (hRWR : RW ⊆ R)
    (hPWR : PW ⊆ R) :
    (∀ z ∈ KW, (A.neighborFinset z ∩ Y).card = b) ∧
      (∀ z ∈ RW, (A.neighborFinset z ∩ Y).card = b - 1) ∧
      ∀ z ∈ PW, (A.neighborFinset z ∩ Y).card = b - 1 := by
  have hcases := uniform_Y_fiber_card_eq_of_indicator_profile
    A Y R b hprofile
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact hcases.1 z (Finset.disjoint_left.mp hKWR hz)
  · intro z hz
    exact hcases.2 z (hRWR hz)
  · intro z hz
    exact hcases.2 z (hPWR hz)

end


end Erdos85

#print axioms Erdos85.uniform_Y_fiber_card_eq_of_indicator_profile
#print axioms Erdos85.uniform_Y_wing_fiber_sizes
