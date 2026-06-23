/-
  Recursive Computation of Unit Ball Volumes
  Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-01

  Question: Can the Gamma function values ω_n (unit n-ball volumes) be computed
  for all n via a recursive formula?

  Answer: YES. The recurrence ω_{n+2} = (2π/(n+2)) · ω_n holds for all n ≥ 0,
  following directly from the Gamma function identity Γ(z+1) = z·Γ(z).

  Combined with the base cases ω_0 = 1 and ω_1 = 2, this gives a complete
  recursive computation of all unit ball volumes without evaluating Γ directly.

  Chain: area-of-circle → OQ01 → OQ02 → OQ01 → **OQ01 (THIS FILE)**

  References:
  - AreaOfCircleOQ01OQ02OQ01.lean (parent: defines unitBallVolume, proves n=0,1,2,3)
  - <https://en.wikipedia.org/wiki/Volume_of_an_n-ball#Recurrences>
-/

import Mathlib

open Real

noncomputable section

namespace UnitBallRecurrence

/-- The unit n-ball volume ω_n = π^(n/2) / Γ(n/2 + 1).
    Matches NDimVolumeIntegral.unitBallVolume from the parent file. -/
def ω (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/- ## Part I: Base Cases -/

/-- ω_0 = 1 (a single point). -/
theorem omega_zero : ω 0 = 1 := by
  unfold ω
  simp [Gamma_one]

/-- ω_1 = 2 (the interval [-1,1]). -/
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

/- ## Part II: Positivity -/

/-- ω_n > 0 for all n. -/
theorem omega_pos (n : ℕ) : 0 < ω n := by
  unfold ω
  apply div_pos
  · exact rpow_pos_of_pos pi_pos _
  · exact Gamma_pos_of_pos (by positivity)

/-- Γ(n/2 + 1) > 0 for all n : ℕ. -/
theorem gamma_half_pos (n : ℕ) : 0 < Gamma ((n : ℝ) / 2 + 1) :=
  Gamma_pos_of_pos (by positivity)

/- ## Part III: The Recurrence (Main Theorem) -/

/-- **MAIN THEOREM**: The unit ball volume satisfies the two-step recurrence
    ω_{n+2} = (2π / (n+2)) · ω_n for all n ≥ 0.

    Proof outline:
    - ω_{n+2} = π^((n+2)/2) / Γ((n+2)/2 + 1)
    - (n+2)/2 = n/2 + 1, so π^((n+2)/2) = π · π^(n/2)
    - Γ((n+2)/2 + 1) = Γ(n/2 + 2) = (n/2 + 1) · Γ(n/2 + 1)  [Gamma recurrence]
    - Therefore ω_{n+2} = π/(n/2 + 1) · ω_n = 2π/(n+2) · ω_n -/
theorem omega_recurrence (n : ℕ) :
    ω (n + 2) = 2 * π / (↑n + 2) * ω n := by
  unfold ω
  -- Cast arithmetic: (n+2)/2 = n/2 + 1 and (n+2)/2 + 1 = n/2 + 2
  have hcast1 : (↑(n + 2) : ℝ) / 2 = ↑n / 2 + 1 := by push_cast; ring
  have hcast2 : (↑(n + 2) : ℝ) / 2 + 1 = ↑n / 2 + 2 := by push_cast; ring
  rw [hcast1, hcast2]
  -- Split exponent: π^(n/2 + 1) = π^(n/2) · π
  rw [rpow_add pi_pos, rpow_one]
  -- Split Gamma: Γ(n/2 + 2) = (n/2 + 1) · Γ(n/2 + 1)
  have hpos : (0 : ℝ) < ↑n / 2 + 1 := by positivity
  rw [show (↑n : ℝ) / 2 + 2 = (↑n / 2 + 1) + 1 from by ring,
      Gamma_add_one hpos.ne']
  -- Now: π^(n/2) · π / ((n/2 + 1) · Γ(n/2 + 1)) = 2π/(n+2) · (π^(n/2) / Γ(n/2 + 1))
  have hΓ : 0 < Gamma (↑n / 2 + 1) := gamma_half_pos n
  field_simp [hpos.ne', hΓ.ne']
  ring

/- ## Part IV: Computability Corollaries -/

/-- The recurrence reduces ω_{n+2} to ω_n, so any ω_n is computable
    from the base cases ω_0 = 1 and ω_1 = 2 in ⌊n/2⌋ steps. -/

/-- ω_2 = π via the recurrence from ω_0 = 1. -/
theorem omega_two_via_recurrence : ω 2 = π := by
  rw [omega_recurrence 0, omega_zero]
  simp

/-- ω_3 = 4π/3 via the recurrence from ω_1 = 2. -/
theorem omega_three_via_recurrence : ω 3 = 4 * π / 3 := by
  rw [omega_recurrence 1, omega_one]
  push_cast
  ring

/-- ω_4 = π²/2 via the recurrence from ω_2 = π. -/
theorem omega_four_via_recurrence : ω 4 = π ^ 2 / 2 := by
  rw [omega_recurrence 2, omega_two_via_recurrence]
  push_cast
  ring

/-- ω_5 = 8π²/15 via the recurrence from ω_3 = 4π/3. -/
theorem omega_five_via_recurrence : ω 5 = 8 * π ^ 2 / 15 := by
  rw [omega_recurrence 3, omega_three_via_recurrence]
  push_cast
  ring

/- ## Part V: Summary

### Proved (0 sorries, 0 axioms):
1. `omega_zero` — ω_0 = 1
2. `omega_one` — ω_1 = 2
3. `omega_pos` — ω_n > 0 for all n
4. `omega_recurrence` — ω_{n+2} = 2π/(n+2) · ω_n (**MAIN THEOREM**)
5. `omega_two_via_recurrence` — ω_2 = π (computed from recurrence)
6. `omega_three_via_recurrence` — ω_3 = 4π/3
7. `omega_four_via_recurrence` — ω_4 = π²/2
8. `omega_five_via_recurrence` — ω_5 = 8π²/15

### Key Insight:
The recurrence follows from the Gamma function identity Γ(z+1) = z·Γ(z).
Since ω_n = π^(n/2)/Γ(n/2+1), replacing n by n+2 gives an extra factor of π
in the numerator and a factor of (n/2+1) in the denominator from the Gamma
recurrence, yielding the clean formula ω_{n+2} = 2π/(n+2) · ω_n.

### Answer to the OQ:
YES, the Gamma function values ω_n can be computed for all n via the recursive
formula ω_{n+2} = (2π/(n+2))·ω_n with base cases ω_0 = 1 and ω_1 = 2.
(Note: the formula (2π/n)·ω_n in the problem statement has the wrong index;
the correct formula is (2π/(n+2))·ω_n.)
-/

end UnitBallRecurrence

end
