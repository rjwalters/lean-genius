import Proofs.Erdos85ThreeSeparatorPositiveSpikeLocationParity
import Proofs.Erdos85ThreeSeparatorEndpointWingMatching

/-!
# The endpoint punctured parallel class

At the endpoint of the surviving positive-spike branch, the outside-pole
parts of the neighborhoods of the defect-clique shore are pairwise disjoint
and have exactly the cardinality of the ambient complement after removing
the exceptional point.  Hence they exhaust that complement.  This is (B14).
-/

open Finset SimpleGraph

namespace Erdos85

/-- Generic exact-cover form of B14.  `NW` is the union of the neighborhoods
of the three separator poles, and the blocks are the parts of `N_A(x)` lying
outside `NW`. -/
theorem outside_pole_neighborhoods_eq_punctured_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (X W : Finset V) (c : V) (q : ℕ) :
    let NW := W.biUnion fun w => A.neighborFinset w
    let B : V → Finset V := fun x => A.neighborFinset x \ NW
    (X : Set V).PairwiseDisjoint B →
      (∀ x ∈ X, (B x).card = q - 1) →
      (∀ x ∈ X, ¬ A.Adj x c) →
      (Finset.univ \ (NW ∪ {c})).card = X.card * (q - 1) →
      X.biUnion B = Finset.univ \ (NW ∪ {c}) := by
  dsimp only
  intro hdisj hblock hcX hambient
  let NW := W.biUnion fun w => A.neighborFinset w
  let B : V → Finset V := fun x => A.neighborFinset x \ NW
  have hsub : X.biUnion B ⊆ Finset.univ \ (NW ∪ {c}) := by
    intro z hz
    obtain ⟨x, hx, hzB⟩ := Finset.mem_biUnion.mp hz
    have hzParts := Finset.mem_sdiff.mp hzB
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ z, ?_⟩
    intro hzUnion
    rcases Finset.mem_union.mp hzUnion with hzNW | hzc
    · exact hzParts.2 hzNW
    · have hzc' : z = c := Finset.mem_singleton.mp hzc
      subst z
      exact hcX x hx ((A.mem_neighborFinset x c).mp hzParts.1)
  have hcardUnion : (X.biUnion B).card = X.card * (q - 1) := by
    rw [Finset.card_biUnion hdisj]
    calc
      ∑ x ∈ X, (B x).card = ∑ _x ∈ X, (q - 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hblock x hx
      _ = X.card * (q - 1) := by simp
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hambient, hcardUnion]

#print axioms outside_pole_neighborhoods_eq_punctured_complement

end Erdos85
