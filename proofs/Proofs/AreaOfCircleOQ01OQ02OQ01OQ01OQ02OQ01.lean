/-
  Strict Unimodality of Unit Ball Volume: Strict Ascent to the Peak at n=5
  Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-01-oq-02-oq-01

  The parent (AreaOfCircleOQ01OQ02OQ01OQ01OQ02.lean) proves that n=5 is the
  argmax of the unit n-ball volume ω_n = π^(n/2)/Γ(n/2+1): ω_n ≤ ω_5 for all n.
  That is a statement about the *location* of the maximum only.

  This file sharpens it to a statement about the full monotonicity *profile*:
  STRICT UNIMODALITY. We prove the missing strict-ascent half,

      ω_0 < ω_1 < ω_2 < ω_3 < ω_4 < ω_5,

  and combine it with the parent's two-step descent to obtain that n=5 is a
  STRICT global maximum: ω_n < ω_5 for every n ≠ 5. Together these say the
  sequence rises strictly to a single peak at n=5 and stays strictly below it
  everywhere else — there are no plateaus and the maximizer is unique with a
  strict gap.

  The ascent is genuinely elementary: each step reduces to a rational
  comparison of the explicit values ω_0=1, ω_1=2, ω_2=π, ω_3=4π/3, ω_4=π²/2,
  ω_5=8π²/15, needing only the crude bound π > 3 (the sharpest step, ω_4 < ω_5,
  needs no π bound at all — just 15 < 16).

  References:
  - AreaOfCircleOQ01OQ02OQ01OQ01OQ02.lean (parent: argmax + two-step descent)
  - https://en.wikipedia.org/wiki/Volume_of_an_n-ball#Maximum_and_minimum
-/
import Proofs.AreaOfCircleOQ01OQ02OQ01OQ01OQ02

open Real

noncomputable section

namespace MaxBallVolume

/- ## Strict Ascent: the Five Steps to the Peak

   Each `ω k < ω (k+1)` for k ∈ {0,1,2,3,4} reduces, via the parent's explicit
   values, to an elementary inequality. -/

/-- ω_0 = 1 < 2 = ω_1. Pure arithmetic. -/
theorem omega_zero_lt_one : ω 0 < ω 1 := by
  rw [omega_zero, omega_one]; norm_num

/-- ω_1 = 2 < π = ω_2, since π > 3 > 2. -/
theorem omega_one_lt_two : ω 1 < ω 2 := by
  rw [omega_one, omega_two]; linarith [Real.pi_gt_three]

/-- ω_2 = π < 4π/3 = ω_3, since the gap is π/3 > 0. -/
theorem omega_two_lt_three : ω 2 < ω 3 := by
  rw [omega_two, omega_three]; linarith [Real.pi_pos]

/-- ω_3 = 4π/3 < π²/2 = ω_4. Equivalent to 8π < 3π², i.e. 8 < 3π,
    which holds since π > 3 gives 3π > 9 > 8. -/
theorem omega_three_lt_four : ω 3 < ω 4 := by
  rw [omega_three, omega_four]
  nlinarith [Real.pi_gt_three, Real.pi_pos]

/-- ω_4 = π²/2 < 8π²/15 = ω_5. Equivalent to 15 < 16; needs no π bound. -/
theorem omega_four_lt_five : ω 4 < ω 5 := by
  rw [omega_four, omega_five]
  linarith [pow_pos Real.pi_pos 2]

/-- **Strict ascent.** ω is strictly increasing on the initial segment {0,…,5}:
    `m < n ≤ 5 ⟹ ω m < ω n`. Proved by transitivity over the five steps; the
    finite case split closes each pair `(m, n)` by `linarith`. -/
theorem omega_strict_ascent {m n : ℕ} (hmn : m < n) (hn : n ≤ 5) : ω m < ω n := by
  have h01 := omega_zero_lt_one
  have h12 := omega_one_lt_two
  have h23 := omega_two_lt_three
  have h34 := omega_three_lt_four
  have h45 := omega_four_lt_five
  interval_cases n <;> interval_cases m <;> linarith

/- ## Strict Global Maximum -/

/-- n=5 is a **strict** global maximum: ω_n < ω_5 for every n ≠ 5.
    For n < 5 this is the strict ascent; for n > 5 it is the parent's descent
    (each parity subsequence is dominated by ω_6 < ω_5 or ω_7 < ω_5). -/
theorem omega_five_strict_max {n : ℕ} (hn : n ≠ 5) : ω n < ω 5 := by
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact omega_strict_ascent hlt (by omega)
  · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- even n = m + m ≥ 6 ⟹ m ≥ 3, n = 6 + 2*(m-3)
      have h_eq : n = 6 + 2 * (m - 3) := by omega
      rw [h_eq]
      exact lt_of_le_of_lt (omega_even_le_six _) omega_six_lt_five
    · -- odd n = 2*m + 1 ≥ 7 ⟹ m ≥ 3, n = 7 + 2*(m-3)
      have h_eq : n = 7 + 2 * (m - 3) := by omega
      rw [h_eq]
      exact lt_of_le_of_lt (omega_odd_le_seven _) omega_seven_lt_five

/- ## Main Theorem: Strict Unimodality -/

/-- **STRICT UNIMODALITY of the unit ball volume.**

    The two halves of the monotonicity profile:
    * (ascent)      `m < n ≤ 5 ⟹ ω m < ω n` — strictly increasing up to the peak;
    * (strict max)  `n ≠ 5 ⟹ ω n < ω 5`    — strictly below the peak elsewhere.

    Together with the parent's two-step descent (`omega_strict_decrease`), this
    pins down the complete shape: ω rises strictly to a unique peak at n=5 and
    then falls strictly within each parity class — a single strict maximum with
    no plateaus. -/
theorem omega_strictly_unimodal :
    (∀ m n : ℕ, m < n → n ≤ 5 → ω m < ω n) ∧ (∀ n : ℕ, n ≠ 5 → ω n < ω 5) :=
  ⟨fun _ _ h hn => omega_strict_ascent h hn, fun _ h => omega_five_strict_max h⟩

end MaxBallVolume

end
