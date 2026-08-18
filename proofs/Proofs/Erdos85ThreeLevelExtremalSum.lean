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

#print axioms Erdos85.eq_neg_two_of_threeLevel_sum_eq_neg_two_mul_card
#print axioms Erdos85.eq_two_of_threeLevel_sum_eq_two_mul_card

end Erdos85
