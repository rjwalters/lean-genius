/-
  Erdős Problem #236: Growth of p + 2^k Representations

  Source: https://erdosproblems.com/236
  Status: OPEN

  Statement:
  Let f(n) count the number of solutions to n = p + 2^k for prime p and k ≥ 0.
  Is it true that f(n) = o(log n)?

  Known Results:
  - Erdős (1950): There are infinitely many n with f(n) ≫ log log n
  - Erdős conjectured: Only {4, 7, 15, 21, 45, 75, 105} have n - 2^k prime for ALL k
  - Mientka-Weitzenkamp (1969): Verified conjecture up to 2^44
  - Vaughan (1973): Strong upper bound on "all prime" numbers

  What We Can Do:
  1. Define the counting function f(n)
  2. State the main conjecture formally
  3. Verify the "all prime" conjecture for small cases
  4. State the known bounds

  Tags: number-theory, additive-combinatorics, primes, asymptotic-analysis
-/

import Mathlib

open Asymptotics Filter

namespace Erdos236

/-! ## Part I: Core Definitions -/

/-- f(n) counts solutions to n = p + 2^k for prime p and k ≥ 0.

    Examples:
    - f(3) = 1: 3 = 2 + 2^0 (only solution, since 3-2=1 not prime, 3-4<0)
    - f(5) = 2: 5 = 3 + 2^1 = 2 + 2^0 + ... wait, 5 = 3 + 2 or 5 = ? + 1
      Actually: 5 - 1 = 4 (not prime), 5 - 2 = 3 (prime), 5 - 4 = 1 (not prime)
      So f(5) = 1 (only 5 = 3 + 2^1)
    - f(9) = 2: 9 - 1 = 8 (no), 9 - 2 = 7 (yes), 9 - 4 = 5 (yes), 9 - 8 = 1 (no)
      So f(9) = 2 (9 = 7 + 2 = 5 + 4) -/
def f (n : ℕ) : ℕ :=
  ((List.range (Nat.log2 n + 1)).filter (fun k => Nat.Prime (n - 2^k))).length

/-! ## Part II: Basic Properties -/

/-- For any n > 0, f(n) is at most log₂(n) + 1 (trivial upper bound). -/
theorem f_trivial_upper_bound (n : ℕ) (hn : n > 0) :
    f n ≤ Nat.log2 n + 1 := by
  unfold f
  calc ((List.range (Nat.log2 n + 1)).filter (fun k => Nat.Prime (n - 2^k))).length
      ≤ (List.range (Nat.log2 n + 1)).length := List.length_filter_le _ _
    _ = Nat.log2 n + 1 := List.length_range (Nat.log2 n + 1)

/-- f(2) = 0: No way to write 2 = p + 2^k with p prime.
    2 - 1 = 1 (not prime), 2 - 2 = 0 (not prime) -/
theorem f_two : f 2 = 0 := by native_decide

/-- f(3) = 1: 3 = 2 + 2^0 is the only representation. -/
theorem f_three : f 3 = 1 := by native_decide

/-- f(5) = 1: 5 = 3 + 2^1 is the only representation. -/
theorem f_five : f 5 = 1 := by native_decide

/-- f(9) = 2: 9 = 7 + 2 = 5 + 4. -/
theorem f_nine : f 9 = 2 := by native_decide

/-- f(15) = 3: 15 = 13 + 2 = 11 + 4 = 7 + 8. -/
theorem f_fifteen : f 15 = 3 := by native_decide

/-! ## Part III: Special Numbers (All-Prime Property) -/

/-- A number n has the "all-prime" property if n - 2^k is prime for ALL
    1 < 2^k < n. These are extremely rare.

    Erdős conjectured the complete list is {4, 7, 15, 21, 45, 75, 105}. -/
def HasAllPrimeProperty (n : ℕ) : Prop :=
  ∀ k : ℕ, 1 < 2^k → 2^k < n → Nat.Prime (n - 2^k)

/-- 4 has the all-prime property: 4 - 2 = 2 (prime). Only k=1 applies. -/
theorem four_all_prime : HasAllPrimeProperty 4 := by
  intro k hk1 hk4
  have hk_bound : k ≤ 1 := by
    by_contra h; push_neg at h
    have : 2^k ≥ 2^2 := Nat.pow_le_pow_right (by omega) h
    omega
  interval_cases k <;> [simp at hk1; native_decide]

/-- 7 has the all-prime property: 7 - 2 = 5, 7 - 4 = 3 (both prime). -/
theorem seven_all_prime : HasAllPrimeProperty 7 := by
  intro k hk1 hk7
  have hk_bound : k ≤ 2 := by
    by_contra h; push_neg at h
    have : 2^k ≥ 2^3 := Nat.pow_le_pow_right (by omega) h
    omega
  interval_cases k <;> [simp at hk1; native_decide; native_decide]

/-- 15 has the all-prime property: 15 - 2 = 13, 15 - 4 = 11, 15 - 8 = 7. -/
theorem fifteen_all_prime : HasAllPrimeProperty 15 := by
  intro k hk1 hk15
  have hk_bound : k ≤ 3 := by
    by_contra h; push_neg at h
    have : 2^k ≥ 2^4 := Nat.pow_le_pow_right (by omega) h
    omega
  interval_cases k <;> [simp at hk1; native_decide; native_decide; native_decide]

/-- 21 has the all-prime property: 21 - 2 = 19, 21 - 4 = 17, 21 - 8 = 13, 21 - 16 = 5. -/
theorem twentyone_all_prime : HasAllPrimeProperty 21 := by
  intro k hk1 hk21
  have hk_bound : k ≤ 4 := by
    by_contra h; push_neg at h
    have : 2^k ≥ 2^5 := Nat.pow_le_pow_right (by omega) h
    omega
  interval_cases k <;> [simp at hk1; native_decide; native_decide; native_decide; native_decide]

/-- The Erdős-Guy conjecture: These are the ONLY numbers with all-prime property.
    Verified up to 2^44 by Mientka-Weitzenkamp (1969).

    We state this as an axiom since it remains unproven in general. -/
axiom erdos_guy_all_prime_conjecture :
  {n : ℕ | HasAllPrimeProperty n ∧ n > 1} = {4, 7, 15, 21, 45, 75, 105}

/-! ## Part IV: Main Conjecture and Known Bounds -/

/-- **Erdős Problem #236** (Main Conjecture): f(n) = o(log n)

    This asks whether, for any ε > 0, we have f(n) < ε · log n for large enough n.
    Equivalently: lim_{n→∞} f(n) / log n = 0. -/
def Erdos236_Conjecture : Prop :=
  (fun n => (f n : ℝ)) =o[atTop] (fun n => Real.log (n : ℝ))

/-- Erdős's lower bound (1950): f(n) ≫ log log n infinitely often.

    This shows f can grow at least as fast as log log n for some n.
    It provides evidence that the conjecture is tight. -/
axiom erdos_lower_bound :
  ∀ C : ℝ, ∀ᶠ n in atTop, ∃ m ≥ n, (f m : ℝ) ≥ C * Real.log (Real.log m)

/-- Vaughan's upper bound (1973): The set of "all-prime" numbers is sparse.

    The number of n ≤ N with HasAllPrimeProperty is at most
    exp(-c · (log log log N / log log N) · log N) · N
    for some constant c > 0.

    This is a strong decay estimate. -/
axiom vaughan_all_prime_sparse :
  ∃ c : ℝ, c > 0 ∧
  ∀ᶠ N in atTop,
    Set.ncard {n : ℕ | n ≤ N ∧ HasAllPrimeProperty n} ≤
      N * Real.exp (-c * (Real.log (Real.log (Real.log N)) /
                         Real.log (Real.log N)) * Real.log N)

/-! ## Part V: Relationship to Problem #10 -/

/-- Connection: This problem is about counting representations n = p + 2^k,
    while Problem #10 asks if every n has such a representation for some k.

    Note: Here we allow k = 0 (so 2^0 = 1), unlike some formulations.

    For n with f(n) = 0, there is NO way to write n = p + 2^k.
    Example: n = 262 has f(262) = 0 (shown in Erdos10PrimePlusPowers). -/
def HasRepresentation (n : ℕ) : Prop := f n > 0

/-- Numbers without any p + 2^k representation have f = 0. -/
theorem no_representation_iff_f_zero (n : ℕ) :
    ¬HasRepresentation n ↔ f n = 0 := by
  simp only [HasRepresentation, Nat.not_lt, Nat.le_zero]

/-! ## Summary -/

/-- Main results in this file:
    1. Definition of f(n) = #{k : n - 2^k is prime}
    2. Verified values: f(2)=0, f(3)=1, f(5)=1, f(9)=2, f(15)=3
    3. "All-prime" property and verified examples {4, 7, 15, 21}
    4. Erdős-Guy conjecture (axiom): exactly 7 all-prime numbers
    5. Main conjecture: f(n) = o(log n) (OPEN)
    6. Erdős lower bound: f(n) ≫ log log n infinitely often
    7. Vaughan upper bound: all-prime numbers are sparse -/
theorem summary :
    f 9 = 2 ∧ HasAllPrimeProperty 15 ∧
    (Erdos236_Conjecture ↔ (fun n => (f n : ℝ)) =o[atTop] (fun n => Real.log n)) :=
  ⟨f_nine, fifteen_all_prime, Iff.rfl⟩

end Erdos236
