import Proofs.Erdos85ThreeSeparatorExceptionalPointWCrossMatching

/-!
# The internal matching in the separator branch

Under B17W', the internal X-profile is `deg_A[X](x)=1-1_K(x)`.
Thus the two K-points are isolated and every remaining point has a unique
remaining neighbor.  This is the internal-matching assertion following
(B17W'').
-/

open Finset SimpleGraph

namespace Erdos85

/-- The profile `deg_A[X] + 1_K = 1` splits `A[X]` into isolated K-points
and a degree-one graph on `X \ K`. -/
theorem internal_matching_and_isolates_of_indicator_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X K : Finset V)
    (hprofile : ∀ x ∈ X,
      (A.neighborFinset x ∩ X).card + (if x ∈ K then 1 else 0) = 1) :
    (∀ z ∈ K ∩ X, A.neighborFinset z ∩ X = ∅) ∧
      ∀ x ∈ X \ K, ∃! y, y ∈ X \ K ∧ A.Adj x y := by
  have hKzero : ∀ z ∈ K ∩ X, A.neighborFinset z ∩ X = ∅ := by
    intro z hz
    have hzParts := Finset.mem_inter.mp hz
    have hzero := hprofile z hzParts.2
    simp [hzParts.1] at hzero
    exact hzero
  refine ⟨hKzero, ?_⟩
  intro x hx
  have hxParts := Finset.mem_sdiff.mp hx
  have hdegX : (A.neighborFinset x ∩ X).card = 1 := by
    have := hprofile x hxParts.1
    simp [hxParts.2] at this
    exact this
  have heq : A.neighborFinset x ∩ (X \ K) = A.neighborFinset x ∩ X := by
    apply Finset.Subset.antisymm
    · intro y hy
      have hyParts := Finset.mem_inter.mp hy
      exact Finset.mem_inter.mpr
        ⟨hyParts.1, (Finset.mem_sdiff.mp hyParts.2).1⟩
    · intro y hy
      have hyParts := Finset.mem_inter.mp hy
      apply Finset.mem_inter.mpr
      refine ⟨hyParts.1, Finset.mem_sdiff.mpr ⟨hyParts.2, ?_⟩⟩
      intro hyK
      have hyKX : y ∈ K ∩ X := Finset.mem_inter.mpr ⟨hyK, hyParts.2⟩
      have hzero := hKzero y hyKX
      have hxmem : x ∈ A.neighborFinset y ∩ X := by
        refine Finset.mem_inter.mpr ⟨?_, hxParts.1⟩
        exact (A.mem_neighborFinset y x).mpr
          ((A.mem_neighborFinset x y).mp hyParts.1).symm
      rw [hzero] at hxmem
      simpa using hxmem
  apply existsUnique_adj_of_neighborFinset_inter_card_one A x (X \ K)
  rw [heq]
  exact hdegX

#print axioms internal_matching_and_isolates_of_indicator_profile

end Erdos85
