import Proofs.Erdos85OneHighOddProfileRepeatedTwoEdgeOwner
import Proofs.Erdos85OneHighOddProfileRepeatedOwnerPair

/-!
# Decode the repeated two-edge owner to a specific witness pair

The sharp selector records an owner occurring at least twice among six
endpoints.  Since each individual partition witness has distinct endpoints,
those occurrences belong to two different witnesses.  This module retains
that pair together with the owner's two-internal-edge property.
-/

namespace Erdos85

/-- If a value occurs twice among three genuine pairs, it belongs to two
different pairs. -/
theorem three_pairEdges_count_two_exists_pairwise_shared
    {L : Type*} [DecidableEq L]
    (a₀ b₀ a₁ b₁ a₂ b₂ z : L)
    (h₀ : a₀ ≠ b₀) (h₁ : a₁ ≠ b₁) (h₂ : a₂ ≠ b₂)
    (hcount : 2 <= [a₀, b₀, a₁, b₁, a₂, b₂].count z) :
    (z ∈ ({a₀, b₀} : Finset L) ∧ z ∈ ({a₁, b₁} : Finset L)) ∨
    (z ∈ ({a₀, b₀} : Finset L) ∧ z ∈ ({a₂, b₂} : Finset L)) ∨
    (z ∈ ({a₁, b₁} : Finset L) ∧ z ∈ ({a₂, b₂} : Finset L)) := by
  by_cases ha₀ : a₀ = z <;> by_cases hb₀ : b₀ = z <;>
    by_cases ha₁ : a₁ = z <;> by_cases hb₁ : b₁ = z <;>
    by_cases ha₂ : a₂ = z <;> by_cases hb₂ : b₂ = z <;>
    simp_all

/-- Decode the sharp selector to three full partition witnesses and the exact
two-edge owner shared by a specified pair. -/
theorem oneHigh_repeatedTwoEdgeOwnerSelection_exists_pairwise_shared
    (profile : Fin 5) (refinement : List (List OneHighLabelPair))
    (hsel : oneHighRefinementHasRepeatedTwoEdgeOwnerSelection
      profile refinement = true) :
    ∃ e₀ e₁ e₂ : Fin 8 × Fin 8,
      OneHighRefinementOwnerPairWitness refinement 0 e₀.1 e₀.2 ∧
      OneHighRefinementOwnerPairWitness refinement 1 e₁.1 e₁.2 ∧
      OneHighRefinementOwnerPairWitness refinement 2 e₂.1 e₂.2 ∧
      ∃ owner : Fin 8,
        oneHighFamilyInternalEdges profile.val owner = 2 ∧
        ((owner ∈ ({e₀.1, e₀.2} : Finset (Fin 8)) ∧
            owner ∈ ({e₁.1, e₁.2} : Finset (Fin 8))) ∨
          (owner ∈ ({e₀.1, e₀.2} : Finset (Fin 8)) ∧
            owner ∈ ({e₂.1, e₂.2} : Finset (Fin 8))) ∨
          (owner ∈ ({e₁.1, e₁.2} : Finset (Fin 8)) ∧
            owner ∈ ({e₂.1, e₂.2} : Finset (Fin 8)))) := by
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, owner, _, hedge, hcount⟩ :=
    (oneHighRefinementHasRepeatedTwoEdgeOwnerSelection_eq_true_iff
      profile refinement).mp hsel
  have hw₀ := oneHighOwnerPairWitness_of_mem_candidates he₀
  have hw₁ := oneHighOwnerPairWitness_of_mem_candidates he₁
  have hw₂ := oneHighOwnerPairWitness_of_mem_candidates he₂
  refine ⟨e₀, e₁, e₂, hw₀, hw₁, hw₂, owner, hedge, ?_⟩
  exact three_pairEdges_count_two_exists_pairwise_shared
    e₀.1 e₀.2 e₁.1 e₁.2 e₂.1 e₂.2 owner
    hw₀.1 hw₁.1 hw₂.1 hcount

end Erdos85

#print axioms Erdos85.three_pairEdges_count_two_exists_pairwise_shared
#print axioms Erdos85.oneHigh_repeatedTwoEdgeOwnerSelection_exists_pairwise_shared
