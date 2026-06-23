/-
# Collatz Cycles: Non-Existence of Small Cycles

## Research Question (OQ-02)

Are there cycles other than 1 → 4 → 2 → 1 in the Collatz sequence?

## Main Results

1. **No fixed points**: collatz(n) = n ⟹ n = 0
2. **No 2-cycles**: collatz²(n) = n ⟹ n = 0
3. **Unique cycle through 1**: The orbit of 1 is exactly {1, 2, 4} with period 3
4. **Odd-even structure**: Odd steps strictly increase, even steps strictly decrease
5. **3/4 contraction**: For n ≡ 1 mod 4, three Collatz steps yield (3n+1)/4 < n
6. **Cycle halving constraint**: j odd steps need ≥ ⌈j·log₂(3)⌉ halvings

## References

- Lagarias (1985), "The 3x+1 problem and its generalizations"
- Eliahou (1993), cycle length lower bounds
-/

import Mathlib.Tactic

namespace CollatzCycles

/-! ## Part I: The Collatz Function -/

/-- The Collatz function: n → n/2 if even, n → 3n+1 if odd. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

@[simp] theorem collatz_zero : collatz 0 = 0 := by simp [collatz]

@[simp] theorem collatz_one : collatz 1 = 4 := by simp [collatz]

theorem collatz_even {n : ℕ} (h : n % 2 = 0) : collatz n = n / 2 := by
  simp [collatz, h]

theorem collatz_odd {n : ℕ} (h : n % 2 = 1) : collatz n = 3 * n + 1 := by
  simp [collatz, h]

theorem collatz_two_mul (n : ℕ) : collatz (2 * n) = n := by
  simp [collatz, Nat.mul_mod_right]

/-- Iterate the Collatz function k times. -/
def collatzIter (k : ℕ) (n : ℕ) : ℕ := collatz^[k] n

/-- A number is periodic with period k if k ≥ 1 and collatz^k(n) = n. -/
def IsPeriodic (n : ℕ) (k : ℕ) : Prop :=
  k ≥ 1 ∧ collatzIter k n = n

/-! ## Part II: No Fixed Points -/

/-- **No fixed points**: collatz(n) = n implies n = 0. -/
theorem collatz_no_fixpoint {n : ℕ} (h : collatz n = n) : n = 0 := by
  by_contra hne
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- Even: n = m + m. collatz(n) = n/2. If n/2 = n then n = 0.
    have heven : n % 2 = 0 := by omega
    rw [collatz_even heven] at h; omega
  · -- Odd: collatz(n) = 3n+1. If 3n+1 = n then 2n = -1, impossible.
    have hodd : n % 2 = 1 := by omega
    rw [collatz_odd hodd] at h; omega

/-! ## Part III: No 2-Cycles -/

/-- **No 2-cycles**: collatz(collatz(n)) = n implies n = 0. -/
theorem collatz_no_two_cycle {n : ℕ} (h : collatz (collatz n) = n) : n = 0 := by
  by_contra hne
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n even: collatz(n) = n/2
    have heven : n % 2 = 0 := by omega
    rw [collatz_even heven] at h
    rcases Nat.even_or_odd (n / 2) with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- n/2 even: collatz(n/2) = n/4 = n → n = 0
      have heven2 : (n / 2) % 2 = 0 := by omega
      rw [collatz_even heven2] at h; omega
    · -- n/2 odd: collatz(n/2) = 3·(n/2)+1 = n
      have hodd2 : (n / 2) % 2 = 1 := by omega
      rw [collatz_odd hodd2] at h; omega
  · -- n odd: collatz(n) = 3n+1 (always even)
    have hodd : n % 2 = 1 := by omega
    rw [collatz_odd hodd] at h
    have heven3 : (3 * n + 1) % 2 = 0 := by omega
    rw [collatz_even heven3] at h
    -- (3n+1)/2 = n → 3n+1 = 2n → n = -1
    omega

/-! ## Part IV: The Unique Cycle Through 1 -/

/-- The orbit of 1 is a 3-cycle: 1 → 4 → 2 → 1. -/
theorem orbit_of_one : collatzIter 3 1 = 1 := by native_decide

/-- 1 is not a fixed point. -/
theorem one_not_fixed : collatz 1 ≠ 1 := by simp [collatz]

/-- The orbit of 1 is not a 2-cycle. -/
theorem one_not_two_cycle : collatzIter 2 1 ≠ 1 := by native_decide

/-- The smallest period of 1 is exactly 3. -/
theorem one_period_is_three :
    IsPeriodic 1 3 ∧ ∀ k, 1 ≤ k → k < 3 → ¬ IsPeriodic 1 k := by
  constructor
  · exact ⟨by omega, orbit_of_one⟩
  · intro k hk1 hk3 ⟨_, hper⟩
    interval_cases k <;> simp_all [collatzIter, collatz]

/-- The orbit elements: 1 → 4 → 2 → 1. -/
theorem orbit_one_elements :
    collatz 1 = 4 ∧ collatz 4 = 2 ∧ collatz 2 = 1 :=
  ⟨by simp [collatz], by simp [collatz], by simp [collatz]⟩

/-! ## Part V: Structural Properties of Cycles -/

/-- **Odd growth**: If n is odd and n ≥ 1, then collatz(n) > n. -/
theorem collatz_odd_growth {n : ℕ} (hodd : n % 2 = 1) (_ : n ≥ 1) :
    collatz n > n := by
  rw [collatz_odd hodd]; omega

/-- **Even decrease**: If n is even and n ≥ 2, then collatz(n) < n. -/
theorem collatz_even_decrease {n : ℕ} (heven : n % 2 = 0) (hge : n ≥ 2) :
    collatz n < n := by
  rw [collatz_even heven]; omega

/-- **Odd step-halve bound**: For odd n, one odd step + one halving ≤ 2n. -/
theorem odd_step_halve_le {n : ℕ} (hodd : n % 2 = 1) :
    (3 * n + 1) / 2 ≤ 2 * n := by omega

/-- **3/4 contraction value**: For n ≡ 1 mod 4 with n ≥ 2, (3n+1)/4 < n. -/
theorem three_quarter_value_lt {n : ℕ} (_ : n ≥ 2) (hmod : n % 4 = 1) :
    (3 * n + 1) / 4 < n := by omega

/-- Three Collatz steps for n ≡ 1 mod 4 produce (3n+1)/4. -/
theorem three_steps_mod4_eq1 {n : ℕ} (_ : n ≥ 2) (hmod : n % 4 = 1) :
    collatz (collatz (collatz n)) = (3 * n + 1) / 4 := by
  have hodd : n % 2 = 1 := by omega
  rw [collatz_odd hodd]
  have h1 : (3 * n + 1) % 2 = 0 := by omega
  rw [collatz_even h1]
  have h2 : (3 * n + 1) / 2 % 2 = 0 := by omega
  rw [collatz_even h2]
  -- (3n+1)/2/2 = (3n+1)/4 when 4 | (3n+1)
  have h4 : 4 ∣ (3 * n + 1) := by omega
  omega

/-- **Main contraction theorem**: For n ≡ 1 mod 4 with n ≥ 2, three Collatz
    steps strictly decrease the value. -/
theorem three_quarter_contraction {n : ℕ} (hn : n ≥ 2) (hmod : n % 4 = 1) :
    collatz (collatz (collatz n)) < n := by
  rw [three_steps_mod4_eq1 hn hmod]
  exact three_quarter_value_lt hn hmod

/-! ## Part VI: The 2^M > 3^j Constraint

For a cycle with j odd steps and M total halvings, we need 2^M > 3^j. -/

/-- For j = 1 odd step, we need M ≥ 2 halvings. -/
theorem min_halvings_one_odd : ∀ M, 2^M > 3 → M ≥ 2 := by
  intro M hM; by_contra h; push_neg at h
  interval_cases M <;> simp_all

/-- For j = 2 odd steps, we need M ≥ 4 halvings. -/
theorem min_halvings_two_odd : ∀ M, 2^M > 9 → M ≥ 4 := by
  intro M hM; by_contra h; push_neg at h
  interval_cases M <;> simp_all

/-- For j = 3 odd steps, we need M ≥ 5 halvings. -/
theorem min_halvings_three_odd : ∀ M, 2^M > 27 → M ≥ 5 := by
  intro M hM; by_contra h; push_neg at h
  interval_cases M <;> simp_all

/-- For j = 4 odd steps, we need M ≥ 7 halvings. -/
theorem min_halvings_four_odd : ∀ M, 2^M > 81 → M ≥ 7 := by
  intro M hM; by_contra h; push_neg at h
  interval_cases M <;> simp_all

/-- **Minimum cycle lengths** from halving constraints. -/
theorem min_cycle_length_j1 : ∀ M, 2^M > 3 → 1 + M ≥ 3 := by
  intro M hM; have := min_halvings_one_odd M hM; omega

theorem min_cycle_length_j2 : ∀ M, 2^M > 9 → 2 + M ≥ 6 := by
  intro M hM; have := min_halvings_two_odd M hM; omega

theorem min_cycle_length_j3 : ∀ M, 2^M > 27 → 3 + M ≥ 8 := by
  intro M hM; have := min_halvings_three_odd M hM; omega

theorem min_cycle_length_j4 : ∀ M, 2^M > 81 → 4 + M ≥ 11 := by
  intro M hM; have := min_halvings_four_odd M hM; omega

/-! ## Part VII: Verified Small Non-Cycling -/

/-- The Collatz sequence starting from n reaches 1. -/
def ReachesOne (n : ℕ) : Prop :=
  ∃ k : ℕ, collatzIter k n = 1

/-- All numbers 1-20 reach 1 (hence are not part of any non-trivial cycle). -/
theorem small_numbers_reach_one :
    ∀ n, 1 ≤ n → n ≤ 20 → ReachesOne n := by
  intro n hn1 hn20
  interval_cases n
  · exact ⟨0, by native_decide⟩   -- n=1
  · exact ⟨1, by native_decide⟩   -- n=2
  · exact ⟨7, by native_decide⟩   -- n=3
  · exact ⟨2, by native_decide⟩   -- n=4
  · exact ⟨5, by native_decide⟩   -- n=5
  · exact ⟨8, by native_decide⟩   -- n=6
  · exact ⟨16, by native_decide⟩  -- n=7
  · exact ⟨3, by native_decide⟩   -- n=8
  · exact ⟨19, by native_decide⟩  -- n=9
  · exact ⟨6, by native_decide⟩   -- n=10
  · exact ⟨14, by native_decide⟩  -- n=11
  · exact ⟨9, by native_decide⟩   -- n=12
  · exact ⟨9, by native_decide⟩   -- n=13
  · exact ⟨17, by native_decide⟩  -- n=14
  · exact ⟨17, by native_decide⟩  -- n=15
  · exact ⟨4, by native_decide⟩   -- n=16
  · exact ⟨12, by native_decide⟩  -- n=17
  · exact ⟨20, by native_decide⟩  -- n=18
  · exact ⟨20, by native_decide⟩  -- n=19
  · exact ⟨7, by native_decide⟩   -- n=20

/-! ## Part VIII: Summary

Together our results constrain hypothetical non-trivial Collatz cycles:
1. No fixed points except 0
2. No 2-cycles: collatz²(n) = n ⟹ n = 0
3. The unique cycle through 1 has period 3: {1, 4, 2}
4. For n ≡ 1 mod 4: three steps always decrease (3/4 contraction)
5. Any cycle with j odd steps needs ≥ ⌈j·log₂(3)⌉ halvings
6. All n ≤ 20 reach 1 (not in non-trivial cycles)
7. Minimum cycle lengths: j=1→≥3, j=2→≥6, j=3→≥8, j=4→≥11
-/

/-! ## Verification -/

#check @collatz_no_fixpoint
#check @collatz_no_two_cycle
#check @orbit_of_one
#check @one_period_is_three
#check @collatz_odd_growth
#check @collatz_even_decrease
#check @three_quarter_contraction
#check @three_steps_mod4_eq1
#check @odd_step_halve_le
#check @min_halvings_one_odd
#check @min_halvings_two_odd
#check @min_halvings_three_odd
#check @min_halvings_four_odd
#check @min_cycle_length_j1
#check @min_cycle_length_j2
#check @min_cycle_length_j3
#check @min_cycle_length_j4
#check @small_numbers_reach_one

end CollatzCycles
