import Mathlib

/-! # Extremal sums for three-level integer weights

Small helper lemmas for the signed-vector arguments in the binary square-order
campaign.  If every weight is one of `-2, 0, 2`, attaining either trivial sum
bound forces every summand to attain the corresponding endpoint.
-/

namespace Erdos85

/-- A `{-2,0,2}`-valued family attaining its lower sum bound is constantly
`-2`. -/
theorem eq_neg_two_of_threeLevel_sum_eq_neg_two_mul_card
    {α : Type*} (s : Finset α) (w : α → ℤ)
    (hlevels : ∀ x ∈ s, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (hsum : ∑ x ∈ s, w x = -2 * (s.card : ℤ))
    {x : α} (hx : x ∈ s) :
    w x = -2 := by
  have hnonneg : ∀ y ∈ s, 0 ≤ w y + 2 := by
    intro y hy
    rcases hlevels y hy with h | h | h <;> omega
  have hshift : ∑ y ∈ s, (w y + 2) = 0 := by
    rw [Finset.sum_add_distrib, hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hxzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hshift x hx
  omega

/-- A `{-2,0,2}`-valued family attaining its upper sum bound is constantly
`2`. -/
theorem eq_two_of_threeLevel_sum_eq_two_mul_card
    {α : Type*} (s : Finset α) (w : α → ℤ)
    (hlevels : ∀ x ∈ s, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (hsum : ∑ x ∈ s, w x = 2 * (s.card : ℤ))
    {x : α} (hx : x ∈ s) :
    w x = 2 := by
  have hnonneg : ∀ y ∈ s, 0 ≤ 2 - w y := by
    intro y hy
    rcases hlevels y hy with h | h | h <;> omega
  have hshift : ∑ y ∈ s, (2 - w y) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  have hxzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hshift x hx
  omega

/-- One step below the upper bound, a three-level family on at least two
indices contains both a zero and a `2`.  This is the exact existence content
needed in the signed-vector bipartite-component argument. -/
theorem exists_zero_and_two_of_threeLevel_sum_eq_two_mul_card_sub_two
    {α : Type*} [DecidableEq α] (s : Finset α) (w : α → ℤ)
    (hcard : 2 ≤ s.card)
    (hlevels : ∀ x ∈ s, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (hsum : ∑ x ∈ s, w x = 2 * (s.card : ℤ) - 2) :
    (∃ x ∈ s, w x = 0) ∧ ∃ x ∈ s, w x = 2 := by
  have hnoNeg : ∀ x ∈ s, w x ≠ -2 := by
    intro x hx hxNeg
    have hle : ∑ y ∈ s.erase x, w y ≤ ∑ _y ∈ s.erase x, (2 : ℤ) := by
      apply Finset.sum_le_sum
      intro y hy
      rcases hlevels y (Finset.mem_of_mem_erase hy) with h | h | h <;> omega
    have herase := Finset.card_erase_of_mem hx
    have hsplit := Finset.sum_erase_add s w hx
    simp only [Finset.sum_const, nsmul_eq_mul] at hle
    omega
  have hzero : ∃ x ∈ s, w x = 0 := by
    by_contra h
    push Not at h
    have hall : ∀ x ∈ s, w x = 2 := by
      intro x hx
      rcases hlevels x hx with hneg | hzero | htwo
      · exact (hnoNeg x hx hneg).elim
      · exact (h x hx hzero).elim
      · exact htwo
    have htop : ∑ x ∈ s, w x = 2 * (s.card : ℤ) := by
      calc
        ∑ x ∈ s, w x = ∑ _x ∈ s, (2 : ℤ) :=
          Finset.sum_congr rfl (fun x hx => hall x hx)
        _ = 2 * (s.card : ℤ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
    omega
  refine ⟨hzero, ?_⟩
  by_contra h
  push Not at h
  have hallZero : ∀ x ∈ s, w x = 0 := by
    intro x hx
    rcases hlevels x hx with hneg | hzero | htwo
    · exact (hnoNeg x hx hneg).elim
    · exact hzero
    · exact (h x hx htwo).elim
  have hsumZero : ∑ x ∈ s, w x = 0 := by
    apply Finset.sum_eq_zero
    exact hallZero
  omega

#print axioms Erdos85.eq_neg_two_of_threeLevel_sum_eq_neg_two_mul_card
#print axioms Erdos85.eq_two_of_threeLevel_sum_eq_two_mul_card
#print axioms
  Erdos85.exists_zero_and_two_of_threeLevel_sum_eq_two_mul_card_sub_two

end Erdos85
