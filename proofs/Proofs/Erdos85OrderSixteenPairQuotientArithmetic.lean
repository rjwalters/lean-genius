import Mathlib

/-! # Arithmetic terminal for the H16 exterior-pair quotient -/

namespace Erdos85

/-- Necessary quotient conditions for a six-regular graph commuting with a
two-factor whose component orders are `s`. -/
def SixRegularPairQuotientFeasible {k : ℕ}
    (s : Fin k → ℕ) (q : Fin k → Fin k → ℕ) : Prop :=
  (∀ i, ∑ j, q i j = 6) ∧
  (∀ i j, s i * q i j = s j * q j i) ∧
  (∀ i, q i i + 3 ≤ s i) ∧
  (∀ i j, q i j ≤ s j)

private theorem sum_fin_two (f : Fin 2 → ℕ) :
    (∑ i, f i) = f 0 + f 1 := by
  simp [Fin.sum_univ_succ]

private theorem sum_fin_three (f : Fin 3 → ℕ) :
    (∑ i, f i) = f 0 + f 1 + f 2 := by
  simp [Fin.sum_univ_succ, add_assoc]

private theorem sum_fin_four (f : Fin 4 → ℕ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp [Fin.sum_univ_succ, add_assoc]

theorem not_pairQuotientFeasible_thirteen_three
    (q : Fin 2 → Fin 2 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![13, 3] q := by
  rintro ⟨hrow, hbal, hdiag, hbound⟩
  have hr0 := hrow 0
  have hr1 := hrow 1
  rw [sum_fin_two] at hr0 hr1
  have hb := hbal 0 1
  have hd1 := hdiag 1
  have hu01 := hbound 0 1
  have hu10 := hbound 1 0
  norm_num at hb hd1 hu01 hu10
  omega

theorem not_pairQuotientFeasible_eleven_five
    (q : Fin 2 → Fin 2 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![11, 5] q := by
  rintro ⟨hrow, hbal, hdiag, hbound⟩
  have hr0 := hrow 0
  have hr1 := hrow 1
  rw [sum_fin_two] at hr0 hr1
  have hb := hbal 0 1
  have hd0 := hdiag 0
  have hd1 := hdiag 1
  have hu01 := hbound 0 1
  have hu10 := hbound 1 0
  norm_num at hb hd0 hd1 hu01 hu10
  omega

theorem not_pairQuotientFeasible_nine_seven
    (q : Fin 2 → Fin 2 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![9, 7] q := by
  rintro ⟨hrow, hbal, hdiag, hbound⟩
  have hr0 := hrow 0
  have hr1 := hrow 1
  rw [sum_fin_two] at hr0 hr1
  have hb := hbal 0 1
  have hd0 := hdiag 0
  have hd1 := hdiag 1
  have hu01 := hbound 0 1
  have hu10 := hbound 1 0
  norm_num at hb hd0 hd1 hu01 hu10
  omega

private theorem extract_pairQuotientFeasible_three
    (a b c : ℕ) (q : Fin 3 → Fin 3 → ℕ)
    (h : SixRegularPairQuotientFeasible ![a, b, c] q) :
    q 0 0 + q 0 1 + q 0 2 = 6 ∧
    q 1 0 + q 1 1 + q 1 2 = 6 ∧
    q 2 0 + q 2 1 + q 2 2 = 6 ∧
    a * q 0 1 = b * q 1 0 ∧ a * q 0 2 = c * q 2 0 ∧
    b * q 1 2 = c * q 2 1 ∧
    q 0 0 + 3 ≤ a ∧ q 1 1 + 3 ≤ b ∧ q 2 2 + 3 ≤ c ∧
    q 0 1 ≤ b ∧ q 0 2 ≤ c ∧ q 1 0 ≤ a ∧ q 1 2 ≤ c ∧
    q 2 0 ≤ a ∧ q 2 1 ≤ b := by
  rcases h with ⟨hrow, hbal, hdiag, hbound⟩
  have hr0 := hrow 0
  have hr1 := hrow 1
  have hr2 := hrow 2
  rw [sum_fin_three] at hr0 hr1 hr2
  have hb01 := hbal 0 1
  have hb02 := hbal 0 2
  have hb12 := hbal 1 2
  have hd0 := hdiag 0
  have hd1 := hdiag 1
  have hd2 := hdiag 2
  have hu01 := hbound 0 1
  have hu02 := hbound 0 2
  have hu10 := hbound 1 0
  have hu12 := hbound 1 2
  have hu20 := hbound 2 0
  have hu21 := hbound 2 1
  simp at hb01 hb02 hb12 hd0 hd1 hd2 hu01 hu02 hu10 hu12 hu20 hu21
  exact ⟨hr0, hr1, hr2, hb01, hb02, hb12, hd0, hd1, hd2,
    hu01, hu02, hu10, hu12, hu20, hu21⟩

theorem not_pairQuotientFeasible_ten_three_three
    (q : Fin 3 → Fin 3 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![10, 3, 3] q := by
  intro h
  rcases extract_pairQuotientFeasible_three 10 3 3 q h with
    ⟨hr0, hr1, hr2, hb01, hb02, hb12, hd0, hd1, hd2,
      hu01, hu02, hu10, hu12, hu20, hu21⟩
  omega

theorem not_pairQuotientFeasible_eight_five_three
    (q : Fin 3 → Fin 3 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![8, 5, 3] q := by
  intro h
  rcases extract_pairQuotientFeasible_three 8 5 3 q h with
    ⟨hr0, hr1, hr2, hb01, hb02, hb12, hd0, hd1, hd2,
      hu01, hu02, hu10, hu12, hu20, hu21⟩
  omega

theorem not_pairQuotientFeasible_seven_six_three
    (q : Fin 3 → Fin 3 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![7, 6, 3] q := by
  intro h
  rcases extract_pairQuotientFeasible_three 7 6 3 q h with
    ⟨hr0, hr1, hr2, hb01, hb02, hb12, hd0, hd1, hd2,
      hu01, hu02, hu10, hu12, hu20, hu21⟩
  omega

theorem not_pairQuotientFeasible_six_five_five
    (q : Fin 3 → Fin 3 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![6, 5, 5] q := by
  intro h
  rcases extract_pairQuotientFeasible_three 6 5 5 q h with
    ⟨hr0, hr1, hr2, hb01, hb02, hb12, hd0, hd1, hd2,
      hu01, hu02, hu10, hu12, hu20, hu21⟩
  omega

theorem not_pairQuotientFeasible_seven_three_three_three
    (q : Fin 4 → Fin 4 → ℕ) :
    ¬ SixRegularPairQuotientFeasible ![7, 3, 3, 3] q := by
  rintro ⟨hrow, hbal, hdiag, hbound⟩
  have hr0 := hrow 0
  have hr1 := hrow 1
  have hr2 := hrow 2
  have hr3 := hrow 3
  rw [sum_fin_four] at hr0 hr1 hr2 hr3
  have hb01 := hbal 0 1
  have hb02 := hbal 0 2
  have hb03 := hbal 0 3
  have hb12 := hbal 1 2
  have hb13 := hbal 1 3
  have hb23 := hbal 2 3
  have hd0 := hdiag 0
  have hd1 := hdiag 1
  have hd2 := hdiag 2
  have hd3 := hdiag 3
  have hu01 := hbound 0 1
  have hu02 := hbound 0 2
  have hu03 := hbound 0 3
  have hu10 := hbound 1 0
  have hu12 := hbound 1 2
  have hu13 := hbound 1 3
  have hu20 := hbound 2 0
  have hu21 := hbound 2 1
  have hu23 := hbound 2 3
  have hu30 := hbound 3 0
  have hu31 := hbound 3 1
  have hu32 := hbound 3 2
  simp at hb01 hb02 hb03 hb12 hb13 hb23 hd0 hd1 hd2 hd3 hu01 hu02 hu03 hu10 hu12 hu13 hu20 hu21 hu23 hu30 hu31 hu32
  omega

end Erdos85
