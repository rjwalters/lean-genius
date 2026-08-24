import Proofs.Erdos85IncidenceEqualitySupportArithmetic

/-!
# Balanced signs at full minimum-energy support

An integer vector whose support cardinality equals its squared energy has
only unit entries.  If its coordinate sum is zero, those units split evenly
between the two signs.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

theorem eq_one_or_neg_one_of_sq_eq_one {z : ℤ} (hz : z ^ 2 = 1) :
    z = 1 ∨ z = -1 := by
  exact sq_eq_one_iff.mp hz

/-- Equality between integer support size and squared energy forces every
supported coordinate to be a signed unit. -/
theorem forall_eq_one_or_neg_one_of_support_card_eq_sum_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℤ)
    (henergy : ∑ i, (f i) ^ 2 =
      ((Finset.univ.filter fun i => f i ≠ 0).card : ℤ)) :
    ∀ i, f i ≠ 0 → f i = 1 ∨ f i = -1 := by
  intro i hi
  let S := Finset.univ.filter fun j => f j ≠ 0
  have hiS : i ∈ S := by simp [S, hi]
  have hbase : ∀ j ∈ S.erase i, (1 : ℤ) ≤ (f j) ^ 2 := by
    intro j hj
    have hjne : f j ≠ 0 := (Finset.mem_filter.mp
      (Finset.mem_of_mem_erase hj)).2
    rcases int_sq_eq_one_or_four_le hjne with h1 | h4 <;> omega
  have herase : ((S.erase i).card : ℤ) ≤
      ∑ j ∈ S.erase i, (f j) ^ 2 := by
    calc
      ((S.erase i).card : ℤ) = ∑ _j ∈ S.erase i, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun j hj => hbase j hj
  have hsumS : ∑ j ∈ S, (f j) ^ 2 = (S.card : ℤ) := by
    rw [← henergy]
    apply Finset.sum_subset (by intro j _; simp [S])
    intro j _ hj
    simp [S] at hj
    simp [hj]
  have hsplit := Finset.sum_erase_add S (fun j => (f j) ^ 2) hiS
  have hcardErase : (S.erase i).card + 1 = S.card := by
    rw [Finset.card_erase_of_mem hiS]
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨i, hiS⟩
    omega
  have hsquare : (f i) ^ 2 = 1 := by
    rcases int_sq_eq_one_or_four_le hi with h1 | h4
    · exact h1
    · push_cast at hcardErase
      rw [hsumS] at hsplit
      omega
  exact eq_one_or_neg_one_of_sq_eq_one hsquare

/-- At zero total sum, full minimum-energy support has equally many `+1`
and `-1` entries. -/
theorem balanced_sign_card_of_support_card_eq_energy_of_sum_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℤ) {q : ℕ}
    (hsupport : (Finset.univ.filter fun i => f i ≠ 0).card = q)
    (henergy : ∑ i, (f i) ^ 2 = (q : ℤ))
    (hsum : ∑ i, f i = 0) :
    2 * (Finset.univ.filter fun i => f i = 1).card = q ∧
      2 * (Finset.univ.filter fun i => f i = -1).card = q := by
  let S := Finset.univ.filter fun i => f i ≠ 0
  let P := Finset.univ.filter fun i => f i = 1
  let N := Finset.univ.filter fun i => f i = -1
  have hunit : ∀ i, f i ≠ 0 → f i = 1 ∨ f i = -1 := by
    apply forall_eq_one_or_neg_one_of_support_card_eq_sum_sq f
    rw [henergy, hsupport]
  have hSPN : S = P ∪ N := by
    ext i
    simp only [S, P, N, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · exact hunit i
    · rintro (h | h) <;> omega
  have hdisj : Disjoint P N := by
    rw [Finset.disjoint_left]
    intro i hiP hiN
    have hp : f i = 1 := (Finset.mem_filter.mp hiP).2
    have hn : f i = -1 := (Finset.mem_filter.mp hiN).2
    omega
  have hcardPN : P.card + N.card = q := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hSPN, hsupport]
  have hsumPN : (P.card : ℤ) - (N.card : ℤ) = 0 := by
    rw [← hsum]
    calc
      (P.card : ℤ) - (N.card : ℤ) =
          (∑ _i ∈ P, (1 : ℤ)) + ∑ _i ∈ N, (-1 : ℤ) := by
            simp
            ring
      _ = ∑ i ∈ P ∪ N, f i := by
        rw [Finset.sum_union hdisj]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.mem_filter.mp hi).2.symm
        · apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.mem_filter.mp hi).2.symm
      _ = ∑ i ∈ S, f i := by rw [hSPN]
      _ = ∑ i, f i := by
        apply Finset.sum_subset (by intro i _; simp [S])
        intro i _ hi
        simp [S] at hi
        simp [hi]
  change 2 * P.card = q ∧ 2 * N.card = q
  have hcardPNZ : (P.card : ℤ) + (N.card : ℤ) = (q : ℤ) := by
    exact_mod_cast hcardPN
  constructor <;> omega

end

end Erdos85

#print axioms Erdos85.forall_eq_one_or_neg_one_of_support_card_eq_sum_sq
#print axioms Erdos85.balanced_sign_card_of_support_card_eq_energy_of_sum_eq_zero
