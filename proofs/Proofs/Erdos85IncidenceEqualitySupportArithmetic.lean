import Mathlib

/-!
# Support arithmetic at minimum incidence energy

These are the two discrete arithmetic steps in the equality case of the
`q^3` incidence-bottleneck energy bound.
-/

namespace Erdos85

/-- The C4 support sandwich at energy `q` has only three possible support
sizes once `q ≥ 8`. -/
theorem support_card_eq_two_or_pred_or_self_of_mul_le_two_mul
    {q m : ℕ} (hq : 8 ≤ q) (hmlo : 2 ≤ m) (hmhi : m ≤ q)
    (hmul : m * (q - m + 1) ≤ 2 * q) :
    m = 2 ∨ m = q - 1 ∨ m = q := by
  by_cases hm2 : m = 2
  · exact Or.inl hm2
  right
  by_cases hmq : m = q
  · exact Or.inr hmq
  left
  by_contra hmp
  have hm3 : 3 ≤ m := by omega
  have hmq2 : m ≤ q - 2 := by omega
  have hsub : q - m + 1 = q + 1 - m := by omega
  rw [hsub] at hmul
  have hmulZ : (m : ℤ) * ((q : ℤ) + 1 - (m : ℤ)) ≤ 2 * (q : ℤ) := by
    have hmle : m ≤ q + 1 := by omega
    exact_mod_cast hmul
  have hm3Z : (3 : ℤ) ≤ m := by exact_mod_cast hm3
  have hmq2Z : (m : ℤ) ≤ (q : ℤ) - 2 := by
    have hmadd : m + 2 ≤ q := by omega
    have hmaddZ : (m : ℤ) + 2 ≤ (q : ℤ) := by exact_mod_cast hmadd
    omega
  have hqZ : (8 : ℤ) ≤ q := by exact_mod_cast hq
  nlinarith

/-- A nonzero integer square is either one or at least four. -/
theorem int_sq_eq_one_or_four_le {z : ℤ} (hz : z ≠ 0) :
    z ^ 2 = 1 ∨ 4 ≤ z ^ 2 := by
  have habsPos : 0 < z.natAbs := Int.natAbs_pos.mpr hz
  by_cases habs : z.natAbs = 1
  · left
    have hzabs : |z| = 1 := by
      simpa [Int.natCast_natAbs] using congrArg (fun n : ℕ => (n : ℤ)) habs
    nlinarith [sq_abs z]
  · right
    have habs2 : 2 ≤ z.natAbs := by omega
    have hzabs2 : (2 : ℤ) ≤ |z| := by
      simpa [Int.natCast_natAbs] using
        (show (2 : ℤ) ≤ (z.natAbs : ℤ) by exact_mod_cast habs2)
    nlinarith [sq_abs z]

/-- There is no family of `n` nonzero integers whose squared energy is
`n+1`: after the baseline contribution one from each coordinate, the first
possible increase is three. -/
theorem sum_sq_ne_card_add_one_of_forall_ne_zero
    {ι : Type*} [DecidableEq ι] (S : Finset ι) (f : ι → ℤ)
    (hne : ∀ i ∈ S, f i ≠ 0) :
    ∑ i ∈ S, (f i) ^ 2 ≠ (S.card : ℤ) + 1 := by
  intro hsum
  by_cases hall : ∀ i ∈ S, (f i) ^ 2 = 1
  · have : ∑ i ∈ S, (f i) ^ 2 = (S.card : ℤ) := by
      calc
        (∑ i ∈ S, (f i) ^ 2) = ∑ _i ∈ S, (1 : ℤ) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hall i hi
        _ = (S.card : ℤ) := by simp
    omega
  · push_neg at hall
    obtain ⟨j, hjS, hjne⟩ := hall
    have hj4 : (4 : ℤ) ≤ (f j) ^ 2 :=
      (int_sq_eq_one_or_four_le (hne j hjS)).resolve_left hjne
    have hbase : ∀ i ∈ S.erase j, (1 : ℤ) ≤ (f i) ^ 2 := by
      intro i hi
      rcases int_sq_eq_one_or_four_le (hne i (Finset.mem_of_mem_erase hi)) with h1 | h4
      · omega
      · omega
    have herase : ((S.erase j).card : ℤ) ≤
        ∑ i ∈ S.erase j, (f i) ^ 2 := by
      calc
        ((S.erase j).card : ℤ) = ∑ _i ∈ S.erase j, (1 : ℤ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun i hi => hbase i hi
    have hsplit := Finset.sum_erase_add S (fun i => (f i) ^ 2) hjS
    have hcardErase : (S.erase j).card + 1 = S.card := by
      rw [Finset.card_erase_of_mem hjS]
      omega
    push_cast at herase
    omega

/-- Hence an integer vector of support `q-1` cannot have squared energy
exactly `q`. -/
theorem finiteSupport_card_ne_pred_of_sum_sq_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℤ) {q : ℕ} (hq : 1 ≤ q)
    (hsq : ∑ i, (f i) ^ 2 = (q : ℤ)) :
    (Finset.univ.filter fun i => f i ≠ 0).card ≠ q - 1 := by
  intro hcard
  let S := Finset.univ.filter fun i => f i ≠ 0
  have hne : ∀ i ∈ S, f i ≠ 0 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsumS : ∑ i ∈ S, (f i) ^ 2 = (q : ℤ) := by
    rw [← hsq]
    apply Finset.sum_subset (by intro i _; simp [S])
    intro i _ hi
    simp [S] at hi
    simp [hi]
  apply sum_sq_ne_card_add_one_of_forall_ne_zero S f hne
  rw [hsumS, hcard]
  push_cast
  omega

end Erdos85

#print axioms Erdos85.support_card_eq_two_or_pred_or_self_of_mul_le_two_mul
#print axioms Erdos85.sum_sq_ne_card_add_one_of_forall_ne_zero
#print axioms Erdos85.finiteSupport_card_ne_pred_of_sum_sq_eq
