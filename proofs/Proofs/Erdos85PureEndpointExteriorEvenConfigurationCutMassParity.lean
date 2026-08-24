import Proofs.Erdos85PureEndpointExteriorEvenConfigurationCutParity

/-!
# Global cut parity of an even exterior configuration
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Pointwise equality of two parities and even total first mass force even
total second mass. -/
theorem even_sum_right_of_pointwise_even_add_of_even_sum_left
    {α : Type*} [DecidableEq α] (s : Finset α) (a b : α → ℕ)
    (hpoint : ∀ x ∈ s, Even (a x + b x))
    (ha : Even (∑ x ∈ s, a x)) :
    Even (∑ x ∈ s, b x) := by
  have hab : Even (∑ x ∈ s, (a x + b x)) :=
    Finset.even_sum _ hpoint
  have hsplit : (∑ x ∈ s, (a x + b x)) =
      (∑ x ∈ s, a x) + ∑ x ∈ s, b x := by
    rw [sum_add_distrib]
  rw [hsplit] at hab
  exact (Nat.even_add.mp hab).mp ha

end

end Erdos85

#print axioms Erdos85.even_sum_right_of_pointwise_even_add_of_even_sum_left
