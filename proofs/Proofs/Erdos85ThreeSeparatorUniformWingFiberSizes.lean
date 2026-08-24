import Proofs.Erdos85ThreeSeparatorExceptionalFiberEndpointAvoidance

/-!
# Uniform wing-fiber sizes

The shore profile `A 1_X = (a+1)1 - 1_K` determines every X-fiber size:
a K-center has `a` X-neighbors, while a center outside K has `a+1`.
Applied to the K-, R-, and incident-P centers of a wing, this is the local
size statement in (B35).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact dichotomy supplied by the uniform internal profile. -/
theorem uniform_X_fiber_card_eq_of_indicator_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K : Finset V) (a : ℕ)
    (hprofile : ∀ z,
      (A.neighborFinset z ∩ X).card + (if z ∈ K then 1 else 0) = a + 1) :
    (∀ z ∈ K, (A.neighborFinset z ∩ X).card = a) ∧
      ∀ z ∉ K, (A.neighborFinset z ∩ X).card = a + 1 := by
  constructor
  · intro z hzK
    have hp := hprofile z
    simp [hzK] at hp
    omega
  · intro z hzK
    have hp := hprofile z
    simpa [hzK] using hp

/-- B35 packaged for the three kinds of centers in a fixed wing.  `KW` and
`PW` consist of K-centers; `RW` consists of centers outside K. -/
theorem uniform_wing_fiber_sizes
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K KW RW PW : Finset V) (a : ℕ)
    (hprofile : ∀ z,
      (A.neighborFinset z ∩ X).card + (if z ∈ K then 1 else 0) = a + 1)
    (hKWK : KW ⊆ K)
    (hRWK : Disjoint RW K)
    (hPWK : PW ⊆ K) :
    (∀ z ∈ KW, (A.neighborFinset z ∩ X).card = a) ∧
      (∀ z ∈ RW, (A.neighborFinset z ∩ X).card = a + 1) ∧
      ∀ z ∈ PW, (A.neighborFinset z ∩ X).card = a := by
  have hcases := uniform_X_fiber_card_eq_of_indicator_profile
    A X K a hprofile
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    exact hcases.1 z (hKWK hz)
  · intro z hz
    exact hcases.2 z (Finset.disjoint_left.mp hRWK hz)
  · intro z hz
    exact hcases.1 z (hPWK hz)

end

end Erdos85

#print axioms Erdos85.uniform_X_fiber_card_eq_of_indicator_profile
#print axioms Erdos85.uniform_wing_fiber_sizes
