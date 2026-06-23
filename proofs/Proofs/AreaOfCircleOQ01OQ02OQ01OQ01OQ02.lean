/-
  n=5 Maximizes Unit Ball Volume
  Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-01-oq-02

  The unit n-ball volume ω_n = π^(n/2)/Γ(n/2+1) achieves its global maximum at n=5.

  The first several values are:
    ω_0 = 1,  ω_1 = 2,  ω_2 = π ≈ 3.14,  ω_3 = 4π/3 ≈ 4.19,
    ω_4 = π²/2 ≈ 4.93,  ω_5 = 8π²/15 ≈ 5.26,  ω_6 = π³/6 ≈ 5.17, ...

  The sequence increases up to n=5, then decreases to 0 (thin shell limit).
  The turning point: the recurrence ratio 2π/(n+2) crosses 1 at n+2 = 2π ≈ 6.28,
  i.e., between n=4 (ratio = 2π/6 ≈ 1.047) and n=6 (ratio = 2π/8 ≈ 0.785).
  So n=5 is uniquely the global maximizer.

  References:
  - AreaOfCircleOQ01OQ02OQ01OQ01.lean (parent: proves recurrence and ω_0...ω_5)
  - https://en.wikipedia.org/wiki/Volume_of_an_n-ball#Maximum_and_minimum_
-/

import Mathlib

open Real

noncomputable section

namespace MaxBallVolume

/-- The unit n-ball volume ω_n = π^(n/2) / Γ(n/2 + 1). -/
def ω (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/- ## Basic Properties (reproduced for self-containedness) -/

theorem omega_pos (n : ℕ) : 0 < ω n := by
  unfold ω
  apply div_pos
  · exact rpow_pos_of_pos pi_pos _
  · exact Gamma_pos_of_pos (by positivity)

theorem omega_nonneg (n : ℕ) : 0 ≤ ω n := le_of_lt (omega_pos n)

theorem omega_recurrence (n : ℕ) :
    ω (n + 2) = 2 * π / (↑n + 2) * ω n := by
  unfold ω
  -- hcast2 must be applied before hcast1 to avoid pattern loss
  have hcast1 : (↑(n + 2) : ℝ) / 2 = ↑n / 2 + 1 := by push_cast; ring
  have hcast2 : (↑(n + 2) : ℝ) / 2 + 1 = ↑n / 2 + 2 := by push_cast; ring
  rw [hcast2, hcast1, rpow_add pi_pos, rpow_one]
  have hpos : (0 : ℝ) < ↑n / 2 + 1 := by positivity
  rw [show (↑n : ℝ) / 2 + 2 = (↑n / 2 + 1) + 1 from by ring,
      Gamma_add_one hpos.ne']
  have hΓ : 0 < Gamma (↑n / 2 + 1) := Gamma_pos_of_pos (by positivity)
  field_simp [hpos.ne', hΓ.ne']

/- ## Explicit Values -/

theorem omega_zero : ω 0 = 1 := by unfold ω; simp [Gamma_one]

theorem omega_one : ω 1 = 2 := by
  unfold ω
  simp only [Nat.cast_one]
  rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring]
  have h32 : Gamma (3 / 2 : ℝ) = √π / 2 := by
    have h := Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
    rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring] at h
    rw [h, Gamma_one_half_eq]; ring
  rw [h32, ← Real.sqrt_eq_rpow]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  field_simp [hpi.ne']

theorem omega_two : ω 2 = π := by
  rw [omega_recurrence 0, omega_zero]; simp

theorem omega_three : ω 3 = 4 * π / 3 := by
  rw [omega_recurrence 1, omega_one]; push_cast; ring

theorem omega_four : ω 4 = π ^ 2 / 2 := by
  rw [omega_recurrence 2, omega_two]; push_cast; ring

theorem omega_five : ω 5 = 8 * π ^ 2 / 15 := by
  rw [omega_recurrence 3, omega_three]; push_cast; ring

/- ## The Sequence Decreases for n ≥ 5 -/

/-- For n ≥ 5, the recurrence ratio 2π/(n+2) < 1 (since n+2 ≥ 7 > 2π, as π < 3.15). -/
theorem ratio_lt_one (n : ℕ) (hn : 5 ≤ n) : 2 * π / ((n : ℝ) + 2) < 1 := by
  rw [div_lt_one (by positivity)]
  have hπ : π < 3.15 := pi_lt_d2
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- For n ≥ 5, ω(n+2) < ω(n): the sequence strictly decreases two steps at a time. -/
theorem omega_strict_decrease (n : ℕ) (hn : 5 ≤ n) : ω (n + 2) < ω n := by
  rw [omega_recurrence]
  calc 2 * π / ((n : ℝ) + 2) * ω n
      < 1 * ω n := mul_lt_mul_of_pos_right (ratio_lt_one n hn) (omega_pos n)
    _ = ω n := one_mul _

/- ## Subsequence Bounds -/

/-- The even-indexed subsequence starting at ω 6 is nonincreasing. -/
theorem omega_even_le_six (k : ℕ) : ω (6 + 2 * k) ≤ ω 6 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_eq : 6 + 2 * (k + 1) = (6 + 2 * k) + 2 := by ring
    rw [h_eq]
    exact le_trans (le_of_lt (omega_strict_decrease _ (by omega))) ih

/-- The odd-indexed subsequence starting at ω 7 is nonincreasing. -/
theorem omega_odd_le_seven (k : ℕ) : ω (7 + 2 * k) ≤ ω 7 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h_eq : 7 + 2 * (k + 1) = (7 + 2 * k) + 2 := by ring
    rw [h_eq]
    exact le_trans (le_of_lt (omega_strict_decrease _ (by omega))) ih

/- ## Key Comparisons at the Maximum -/

/-- ω 6 < ω 5: equivalently 8π²/15 > π³/6, i.e., 48 > 15π (holds since π < 3.15). -/
theorem omega_six_lt_five : ω 6 < ω 5 := by
  have h6 : ω 6 = π ^ 3 / 6 := by
    rw [omega_recurrence 4, omega_four]; push_cast; ring
  rw [h6, omega_five]
  have hπ2 : (0 : ℝ) < π ^ 2 := pow_pos pi_pos 2
  have h15π : 15 * π < 48 := by linarith [pi_lt_d2]
  -- 15*π^3 < 48*π^2 by multiplying h15π by π^2 > 0
  have key : 15 * π ^ 3 < 48 * π ^ 2 :=
    calc 15 * π ^ 3 = 15 * π * π ^ 2 := by ring
      _ < 48 * π ^ 2 := mul_lt_mul_of_pos_right h15π hπ2
  -- π^3/6 < 8*π^2/15 via common denominator 90
  calc π ^ 3 / 6 = 15 * π ^ 3 / 90 := by ring
    _ < 48 * π ^ 2 / 90 := by gcongr
    _ = 8 * π ^ 2 / 15 := by ring

/-- ω 7 < ω 5: ω(5+2) < ω 5 by strict decrease. -/
theorem omega_seven_lt_five : ω 7 < ω 5 := omega_strict_decrease 5 le_rfl

/- ## Main Theorem -/

/-- **MAIN THEOREM**: The unit ball volume ω_n is maximized at n = 5.
    ω_5 = 8π²/15 ≈ 5.2638 is the global maximum over all dimensions.

    The sequence increases for n ≤ 5 (ratio 2π/(n+2) > 1 for small n)
    and strictly decreases for n ≥ 5 (ratio 2π/(n+2) < 1 for n+2 ≥ 7 > 2π).
    The crossover point n+2 = 2π ≈ 6.28 lies between n=4 and n=6. -/
theorem omega_five_is_max (n : ℕ) : ω n ≤ ω 5 := by
  by_cases hn5 : n ≤ 5
  · -- Finite cases n ∈ {0, 1, 2, 3, 4, 5}
    interval_cases n
    · -- n = 0: 1 ≤ 8π²/15 (π > 3 → π² > 9 → 8π² > 72 > 15)
      rw [omega_zero, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
    · -- n = 1: 2 ≤ 8π²/15 (π > 3 → 8π² > 72 > 30)
      rw [omega_one, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
    · -- n = 2: π ≤ 8π²/15 (equivalent to 15 ≤ 8π, holds since π > 3 > 15/8)
      rw [omega_two, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
    · -- n = 3: 4π/3 ≤ 8π²/15 (equivalent to 5/2 ≤ π, holds since π > 3)
      rw [omega_three, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
    · -- n = 4: π²/2 ≤ 8π²/15 (equivalent to 15 ≤ 16, purely arithmetic)
      rw [omega_four, omega_five]; nlinarith [pow_pos pi_pos 2]
    · exact le_refl _
  · -- n ≥ 6: split into even and odd subsequences
    push_neg at hn5  -- hn5 : 5 < n
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- Even: n = m + m ≥ 6, so m ≥ 3
      have hm_ge : 3 ≤ m := by omega
      have h_eq : n = 6 + 2 * (m - 3) := by omega
      rw [h_eq]
      exact le_trans (omega_even_le_six _) (le_of_lt omega_six_lt_five)
    · -- Odd: n = 2*m+1 ≥ 7 (odd ≥ 6), so m ≥ 3
      have hm_ge : 3 ≤ m := by omega
      have h_eq : n = 7 + 2 * (m - 3) := by omega
      rw [h_eq]
      exact le_trans (omega_odd_le_seven _) (le_of_lt omega_seven_lt_five)

/-- The maximum value of the unit ball volume is 8π²/15. -/
theorem omega_max_value : ∀ n : ℕ, ω n ≤ 8 * π ^ 2 / 15 := fun n =>
  omega_five.symm ▸ omega_five_is_max n

/-- n=5 is the unique natural number achieving the maximum. -/
theorem omega_five_unique_max (n : ℕ) (h : ω 5 ≤ ω n) : n = 5 := by
  by_contra hn
  have hlt : ω n < ω 5 := by
    cases Nat.lt_or_ge n 5 with
    | inl hlt5 =>
      interval_cases n
      · rw [omega_zero, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
      · rw [omega_one, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
      · rw [omega_two, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
      · rw [omega_three, omega_five]; nlinarith [Real.pi_gt_three, pow_pos pi_pos 2]
      · rw [omega_four, omega_five]; nlinarith [pow_pos pi_pos 2]
    | inr hge5 =>
      have hne : n ≠ 5 := hn
      have hgt5 : 5 < n := Nat.lt_of_le_of_ne hge5 (Ne.symm hne)
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hm_ge : 3 ≤ m := by omega
        have h_eq : n = 6 + 2 * (m - 3) := by omega
        rw [h_eq]
        exact lt_of_le_of_lt (omega_even_le_six _) omega_six_lt_five
      · have hm_ge : 3 ≤ m := by omega
        have h_eq : n = 7 + 2 * (m - 3) := by omega
        rw [h_eq]
        exact lt_of_le_of_lt (omega_odd_le_seven _) omega_seven_lt_five
  linarith

end MaxBallVolume

end
