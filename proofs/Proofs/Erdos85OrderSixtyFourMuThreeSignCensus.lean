import Proofs.Erdos85OrderSixtyFourMuThreeCubicTerminal

/-! # Sign census for the order-64 rational mu-three lifts -/

namespace Erdos85

private theorem eq_two_or_eq_neg_two_of_sq_eq_four (a : ℤ)
    (h : a ^ 2 = 4) : a = 2 ∨ a = -2 := by
  have hfac : (a - 2) * (a + 2) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfac with hleft | hright
  · left; omega
  · right; omega

/-- A family of `±2` lifts with total trace `-8` has exactly four more
negative than positive signs.  Consequently its cardinality is four plus
twice the number of positive signs, so in particular at least four rational
`μ=3` lifts are required globally. -/
theorem muThree_sign_census_of_sum_eq_neg_eight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → ℤ) (hsq : ∀ i, α i ^ 2 = 4)
    (hlinear : (∑ i, α i) = -8) :
    ((Finset.univ.filter fun i => α i = -2).card =
        (Finset.univ.filter fun i => α i = 2).card + 4) ∧
      Fintype.card ι =
        2 * (Finset.univ.filter fun i => α i = 2).card + 4 := by
  classical
  let P := Finset.univ.filter fun i => α i = 2
  let N := Finset.univ.filter fun i => α i ≠ 2
  have hneg (i : ι) (hi : i ∈ N) : α i = -2 := by
    have hne : α i ≠ 2 := (Finset.mem_filter.mp hi).2
    exact (eq_two_or_eq_neg_two_of_sq_eq_four (α i) (hsq i)).resolve_left hne
  have hsumSplit : (∑ i, α i) = ∑ i ∈ P, α i + ∑ i ∈ N, α i := by
    simpa [P, N] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset ι)) (p := fun i => α i = 2) α).symm
  have hPsum : (∑ i ∈ P, α i) = (P.card : ℤ) * 2 := by
    calc
      (∑ i ∈ P, α i) = ∑ _i ∈ P, (2 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mem_filter.mp hi).2
      _ = (P.card : ℤ) * 2 := by simp
  have hNsum : (∑ i ∈ N, α i) = (N.card : ℤ) * (-2) := by
    calc
      (∑ i ∈ N, α i) = ∑ _i ∈ N, (-2 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hneg i hi
      _ = (N.card : ℤ) * (-2) := by simp
  have hcountInt : (N.card : ℤ) = (P.card : ℤ) + 4 := by
    rw [hsumSplit, hPsum, hNsum] at hlinear
    omega
  have hcount : N.card = P.card + 4 := by exact_mod_cast hcountInt
  have hpartition : P.card + N.card = Fintype.card ι := by
    simpa [P, N] using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => α i = 2)
  have hNfilter :
      (Finset.univ.filter fun i => α i = -2) = N := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, N]
    constructor
    · intro hi
      omega
    · intro hi
      exact (eq_two_or_eq_neg_two_of_sq_eq_four (α i) (hsq i)).resolve_left hi
  constructor
  · simpa [P, hNfilter] using hcount
  · rw [← hpartition, hcount]
    simp [P]
    omega

/-- Immediate capacity consequence of the sign census. -/
theorem four_le_card_of_muThree_sum_eq_neg_eight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → ℤ) (hsq : ∀ i, α i ^ 2 = 4)
    (hlinear : (∑ i, α i) = -8) : 4 ≤ Fintype.card ι := by
  obtain ⟨_, hcard⟩ := muThree_sign_census_of_sum_eq_neg_eight α hsq hlinear
  rw [hcard]
  omega

end Erdos85
