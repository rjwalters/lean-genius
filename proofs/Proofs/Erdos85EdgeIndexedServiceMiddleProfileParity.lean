import Proofs.Erdos85EdgeIndexedServiceTypeParity

/-! # Parity of the middle same-type service profile -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

private theorem sum_eq_two_mul_filter_two_add_filter_one'
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (hf : ∀ a ∈ s, f a = 0 ∨ f a = 1 ∨ f a = 2) :
    ∑ a ∈ s, f a =
      2 * (s.filter fun a ↦ f a = 2).card +
        (s.filter fun a ↦ f a = 1).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfs : ∀ b ∈ s, f b = 0 ∨ f b = 1 ∨ f b = 2 := by
        intro b hb
        exact hf b (Finset.mem_insert_of_mem hb)
      have hi := ih hfs
      rcases hf a (Finset.mem_insert_self a s) with h0 | h1 | h2
      · simp [Finset.sum_insert, Finset.filter_insert, ha, h0, hi]
      · simp [Finset.sum_insert, Finset.filter_insert, ha, h1, hi] <;> omega
      · simp [Finset.sum_insert, Finset.filter_insert, ha, h2, hi] <;> omega

theorem card_filter_eq_one_even_of_sum_even_of_zero_one_two
    {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (hf : ∀ a ∈ s, f a = 0 ∨ f a = 1 ∨ f a = 2)
    (heven : Even (∑ a ∈ s, f a)) :
    Even (s.filter fun a ↦ f a = 1).card := by
  have hsum := sum_eq_two_mul_filter_two_add_filter_one' s f hf
  rcases heven with ⟨k, hk⟩
  refine ⟨k - (s.filter fun a ↦ f a = 2).card, ?_⟩
  omega

/-- If every central edge of shore type `p` has 0, 1, or 2 same-type service
neighbors, the number with the middle value 1 is even. -/
theorem serviceNeighborShoreTypeCount_middle_profile_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (S : Finset V) (p : ℕ)
    (hprofiles : ∀ a ∈ shoreTypeEdgeFinset R S p,
      serviceNeighborShoreTypeCount R Cedge a S p = 0 ∨
      serviceNeighborShoreTypeCount R Cedge a S p = 1 ∨
      serviceNeighborShoreTypeCount R Cedge a S p = 2) :
    Even ((shoreTypeEdgeFinset R S p).filter fun a ↦
      serviceNeighborShoreTypeCount R Cedge a S p = 1).card := by
  apply card_filter_eq_one_even_of_sum_even_of_zero_one_two
    (shoreTypeEdgeFinset R S p)
    (fun a ↦ serviceNeighborShoreTypeCount R Cedge a S p)
    hprofiles
  exact serviceNeighborShoreTypeCount_same_sum_even R Cedge S p

end

end Erdos85

#print axioms Erdos85.serviceNeighborShoreTypeCount_middle_profile_even
