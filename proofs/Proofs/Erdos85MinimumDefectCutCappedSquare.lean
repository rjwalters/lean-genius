import Proofs.Erdos85TwoSeparatorMantelArithmetic

/-!
# Sharp capped-square arithmetic for a minimum defect cut

The boundary degrees of a minimum shore sum to `2r+1` and are at most `r`.
Their square sum is therefore at most `2r²+1`, attained by `(r,r,1)`.
-/

open Finset

namespace Erdos85

/-- A family bounded by `r` and summing to `2r+1` contains a genuinely
intermediate entry. -/
theorem exists_pos_lt_of_sum_eq_two_mul_add_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ i, f i ≤ r) (hsum : ∑ i, f i = 2 * r + 1) :
    ∃ i, 0 < f i ∧ f i < r := by
  by_contra hnone
  have hdvd_each : ∀ i, r ∣ f i := by
    intro i
    have hi := hbound i
    have hcases : f i = 0 ∨ f i = r := by
      by_cases hz : f i = 0
      · exact Or.inl hz
      · right
        by_contra hne
        have hpos : 0 < f i := Nat.pos_of_ne_zero hz
        have hlt : f i < r := Nat.lt_of_le_of_ne hi hne
        exact hnone ⟨i, hpos, hlt⟩
    rcases hcases with h | h
    · rw [h]
      exact dvd_zero r
    · rw [h]
  have hdvd_sum : r ∣ ∑ i, f i := by
    apply Finset.dvd_sum
    intro i _
    exact hdvd_each i
  rw [hsum] at hdvd_sum
  have hone : r ∣ 1 := by
    have htwo : r ∣ 2 * r := dvd_mul_left r 2
    exact (Nat.dvd_add_iff_right htwo).mpr hdvd_sum
  have hrle : r ≤ 1 := Nat.le_of_dvd (by omega : 0 < 1) hone
  omega

/-- Sharp capped-square bound. -/
theorem sum_sq_le_two_mul_sq_add_one_of_bound_of_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) {r : ℕ} (hr : 2 ≤ r)
    (hbound : ∀ i, f i ≤ r) (hsum : ∑ i, f i = 2 * r + 1) :
    (∑ i, (f i) ^ 2) ≤ 2 * r ^ 2 + 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 :=
    ⟨r - 1, by omega⟩
  obtain ⟨j, hjpos, hjlt⟩ :=
    exists_pos_lt_of_sum_eq_two_mul_add_one f hr hbound hsum
  have hjgap : s + 1 - 1 ≤ f j * (s + 1 - f j) := by
    have hjle : f j ≤ s + 1 := hbound j
    have hsumj : f j + (s + 1 - f j) = s + 1 := Nat.add_sub_of_le hjle
    have hleft : 1 ≤ f j := hjpos
    have hright : 1 ≤ s + 1 - f j := by omega
    obtain ⟨a, ha⟩ : ∃ a, f j = a + 1 := ⟨f j - 1, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, s + 1 - f j = b + 1 :=
      ⟨s + 1 - f j - 1, by omega⟩
    have hb' : s + 1 - (a + 1) = b + 1 := by simpa [ha] using hb
    rw [ha] at hsumj ⊢
    rw [hb'] at hsumj ⊢
    have hnonneg : 0 ≤ a * b := Nat.zero_le _
    have hs : s = a + b + 1 := by omega
    rw [hs]
    simp only [Nat.add_sub_cancel]
    nlinarith
  have hgap : s + 1 - 1 ≤ ∑ i, f i * (s + 1 - f i) := by
    calc
      s + 1 - 1 ≤ f j * (s + 1 - f j) := hjgap
      _ ≤ ∑ i, f i * (s + 1 - f i) := Finset.single_le_sum
        (f := fun i ↦ f i * (s + 1 - f i))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hdecomp : (∑ i, f i * (s + 1 - f i)) + ∑ i, (f i) ^ 2 =
      (s + 1) * ∑ i, f i := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i, (f i * (s + 1 - f i) + f i ^ 2)) =
          ∑ i, (s + 1) * f i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := hbound i
        have hsumi : f i + (s + 1 - f i) = s + 1 := Nat.add_sub_of_le hi
        simp only [pow_two]
        nlinarith
      _ = (s + 1) * ∑ i, f i := by rw [Finset.mul_sum]
  rw [hsum] at hdecomp
  simp only [pow_two] at hdecomp ⊢
  simp at hgap
  ring_nf at hdecomp ⊢
  have hgap' : s ≤ ∑ i, f i * (1 + s - f i) := by
    simpa [Nat.add_comm] using hgap
  nlinarith

end Erdos85

#print axioms Erdos85.exists_pos_lt_of_sum_eq_two_mul_add_one
#print axioms Erdos85.sum_sq_le_two_mul_sq_add_one_of_bound_of_sum
