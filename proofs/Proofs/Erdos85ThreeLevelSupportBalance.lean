import Mathlib

/-! # Balanced support of three-level weights

A zero-sum family taking values in `{-2,0,2}` has equally many positive and
negative entries.  This is the arithmetic bridge from a squared-mass support
count to the signed `4+4` split used in the order-64 `μ = 1` residue.
-/

namespace Erdos85

/-- The sum of a `{-2,0,2}` family is twice its positive-support cardinality
minus twice its negative-support cardinality. -/
theorem threeLevel_sum_eq_two_mul_card_pos_sub_two_mul_card_neg
    {V : Type*} [DecidableEq V]
    (S : Finset V) (w : V → ℤ)
    (hlevels : ∀ x ∈ S, w x = -2 ∨ w x = 0 ∨ w x = 2) :
    ∑ x ∈ S, w x =
      2 * ((S.filter fun x => w x = 2).card : ℤ) -
      2 * ((S.filter fun x => w x = -2).card : ℤ) := by
  let P := S.filter fun x => w x = 2
  let N := S.filter fun x => w x = -2
  calc
    ∑ x ∈ S, w x =
        ∑ x ∈ S, (if w x = 2 then (2 : ℤ)
          else if w x = -2 then -2 else 0) := by
      apply Finset.sum_congr rfl
      intro x hx
      rcases hlevels x hx with h | h | h <;> simp [h]
    _ = 2 * (P.card : ℤ) - 2 * (N.card : ℤ) := by
      have hfilter :
          ((S.filter fun x => ¬ w x = 2).filter fun x => w x = -2) = N := by
        ext x
        simp only [Finset.mem_filter, N]
        constructor
        · rintro ⟨⟨hxS, -⟩, hx⟩
          exact ⟨hxS, hx⟩
        · rintro ⟨hxS, hx⟩
          refine ⟨⟨hxS, ?_⟩, hx⟩
          omega
      simp only [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const,
        nsmul_eq_mul]
      rw [hfilter]
      simp only [P, N, add_zero]
      ring

/-- A zero-sum `{-2,0,2}` family has equally many `2` and `-2` entries, and
its nonzero support has twice that cardinality. -/
theorem threeLevel_zeroSum_support_balance
    {V : Type*} [DecidableEq V]
    (S : Finset V) (w : V → ℤ)
    (hlevels : ∀ x ∈ S, w x = -2 ∨ w x = 0 ∨ w x = 2)
    (hsum : ∑ x ∈ S, w x = 0) :
    (S.filter fun x => w x = 2).card =
        (S.filter fun x => w x = -2).card ∧
      (S.filter fun x => w x ≠ 0).card =
        2 * (S.filter fun x => w x = 2).card := by
  let P := S.filter fun x => w x = 2
  let N := S.filter fun x => w x = -2
  have hsumForm : ∑ x ∈ S, w x =
      2 * (P.card : ℤ) - 2 * (N.card : ℤ) := by
    exact threeLevel_sum_eq_two_mul_card_pos_sub_two_mul_card_neg S w hlevels
  have hPN : P.card = N.card := by
    rw [hsum] at hsumForm
    exact_mod_cast (by omega : (P.card : ℤ) = (N.card : ℤ))
  have hsupport : (S.filter fun x => w x ≠ 0) = P ∪ N := by
    ext x
    by_cases hx : x ∈ S
    · rcases hlevels x hx with h | h | h <;> simp [P, N, hx, h]
    · simp [P, N, hx]
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro x hxP hxN
    have hp : w x = 2 := (Finset.mem_filter.mp hxP).2
    have hn : w x = -2 := (Finset.mem_filter.mp hxN).2
    omega
  refine ⟨hPN, ?_⟩
  rw [hsupport, Finset.card_union_of_disjoint hdisj, hPN]
  omega

end Erdos85

#print axioms Erdos85.threeLevel_zeroSum_support_balance
#print axioms Erdos85.threeLevel_sum_eq_two_mul_card_pos_sub_two_mul_card_neg
