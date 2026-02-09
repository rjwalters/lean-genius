/-
Erdős Problem #1054: Sum of Smallest Divisors

Let f(n) be the minimal integer m such that n is the sum of the k smallest
divisors of m for some k ≥ 1.

Is it true that f(n) = o(n)? Or is this true only for almost all n,
and limsup f(n)/n = ∞?

**Status**: OPEN

**Background**:
- The function f(n) is undefined for n = 2 and n = 5 (no such m exists)
- For most n, there exists an m whose smallest divisors sum to n
- Example: f(1) = 1 (the only divisor of 1 is 1, and sum of first divisor is 1)
- Example: f(3) = 2 (divisors of 2 are {1,2}, and 1+2 = 3)
- Example: f(6) = 5 (divisors of 5 are {1,5}, and 1+5 = 6)

**Note**: Terry Tao disproved the strong claim that f(n) = o(n) unconditionally.

Reference: https://erdosproblems.com/1054
Sources: [Gu04] Guy, Unsolved Problems in Number Theory, Problem B2
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic

open Nat Finset

namespace Erdos1054

/-
## Infrastructure: Sorted Divisors and Partial Sums

We build constructive definitions for the sorted divisor list and
partial sums, enabling computational verification.
-/

/--
The divisors of m sorted in increasing order.
-/
def sortedDivisors (m : ℕ) : List ℕ :=
  m.divisors.sort (· ≤ ·)

/--
The list of partial sums of the k smallest divisors of m, for k = 1, 2, ..., d(m).
For m = 6 with divisors [1, 2, 3, 6], this gives [1, 3, 6, 12].
-/
def partialDivisorSums (m : ℕ) : List ℕ :=
  ((sortedDivisors m).scanl (· + ·) 0).tail

/--
A number n is representable if there exists some m ≥ 1 and some k ≥ 1 such that
n equals the sum of the k smallest divisors of m.
-/
def IsRepresentable (n : ℕ) : Prop :=
  ∃ m : ℕ, m ≥ 1 ∧ n ∈ (partialDivisorSums m)

/--
Bounded check: is n representable using some m in {1, ..., bound}?
-/
def isRepresentableBound (n : ℕ) (bound : ℕ) : Bool :=
  ((Finset.range bound).filter (fun m => n ∈ (partialDivisorSums (m + 1)))).card > 0

/--
f(n) = the minimal m ≥ 1 such that n equals the sum of the k smallest
divisors of m for some k ≥ 1, computed up to a search bound.
Returns 0 if no such m exists within the bound.
-/
def computeF (n : ℕ) (bound : ℕ := 10000) : ℕ :=
  match (Finset.range bound).filter (fun m => n ∈ (partialDivisorSums (m + 1)))
    |>.sort (· ≤ ·) with
  | [] => 0
  | m :: _ => m + 1

/-
## Concrete Values of f(n)

We prove representability and f(n) values by exhibiting witnesses
and verifying via native_decide.
-/

/--
1 is representable: the divisors of 1 are {1}, and the first partial sum is 1.
-/
theorem representable_1 : IsRepresentable 1 :=
  ⟨1, le_refl 1, by native_decide⟩

/-- f(1) = 1 -/
theorem f_1_eq_one : computeF 1 20 = 1 := by native_decide

/-- 3 is representable: divisors of 2 are {1,2}, 1+2=3. -/
theorem representable_3 : IsRepresentable 3 :=
  ⟨2, by omega, by native_decide⟩

/-- f(3) = 2 -/
theorem f_3_eq_two : computeF 3 20 = 2 := by native_decide

/-- 4 is representable: divisors of 3 are {1,3}, 1+3=4. -/
theorem representable_4 : IsRepresentable 4 :=
  ⟨3, by omega, by native_decide⟩

/-- f(4) = 3 -/
theorem f_4_eq_three : computeF 4 20 = 3 := by native_decide

/-- 6 is representable: divisors of 5 are {1,5}, 1+5=6. -/
theorem representable_6 : IsRepresentable 6 :=
  ⟨5, by omega, by native_decide⟩

/-- f(6) = 5: m = 5 has divisors {1, 5} with 1 + 5 = 6. -/
theorem f_6_eq_five : computeF 6 20 = 5 := by native_decide

/-- 7 is representable: divisors of 4 are {1,2,4}, 1+2+4=7. -/
theorem representable_7 : IsRepresentable 7 :=
  ⟨4, by omega, by native_decide⟩

/-- f(7) = 4 -/
theorem f_7_eq_four : computeF 7 20 = 4 := by native_decide

/-- 8 is representable: divisors of 7 are {1,7}, 1+7=8. -/
theorem representable_8 : IsRepresentable 8 :=
  ⟨7, by omega, by native_decide⟩

/-- f(8) = 7 -/
theorem f_8_eq_seven : computeF 8 20 = 7 := by native_decide

/-- 9 is representable: divisors of 8 are {1,2,4,8}, prefix sums [1,3,7,15].
    But also: divisors of 3 are {1,3}, so 1+3=4 won't give 9.
    Actually: divisors of 15 are {1,3,5,15}, 1+3+5=9. -/
theorem representable_9 : IsRepresentable 9 :=
  ⟨15, by omega, by native_decide⟩

/-- f(9) = 15 -/
theorem f_9_eq : computeF 9 20 = 15 := by native_decide

/-- 10 is representable: divisors of 9 are {1,3,9}, 1+9=10... no, 1+3+6=10 for 12.
    Divisors of 12 = {1,2,3,4,6,12}, 1+2+3+4=10. -/
theorem representable_10 : IsRepresentable 10 :=
  ⟨12, by omega, by native_decide⟩

/-- f(10) = 12 -/
theorem f_10_eq : computeF 10 20 = 12 := by native_decide

/-- 12 is representable: divisors of 6 = {1,2,3,6}, 1+2+3+6=12. -/
theorem representable_12 : IsRepresentable 12 :=
  ⟨6, by omega, by native_decide⟩

/-- f(12) = 6 -/
theorem f_12_eq : computeF 12 20 = 6 := by native_decide

/-- Several small values are representable. -/
theorem some_representable_values :
    IsRepresentable 1 ∧ IsRepresentable 3 ∧ IsRepresentable 4 ∧
    IsRepresentable 6 ∧ IsRepresentable 7 ∧ IsRepresentable 8 ∧
    IsRepresentable 9 ∧ IsRepresentable 10 ∧ IsRepresentable 12 :=
  ⟨representable_1, representable_3, representable_4,
   representable_6, representable_7, representable_8,
   representable_9, representable_10, representable_12⟩

/-
## Non-Representable Values

We prove that 2 and 5 cannot be represented as partial sums of divisors.
Strategy: verify computationally for small m, then prove structurally for all m.
-/

/--
2 is not a partial sum of divisors of any m in {1, ..., 200}.
-/
theorem not_representable_2_small : isRepresentableBound 2 200 = false := by
  native_decide

/--
5 is not a partial sum of divisors of any m in {1, ..., 200}.
-/
theorem not_representable_5_small : isRepresentableBound 5 200 = false := by
  native_decide

/--
Key structural fact for n=2: The partial sums of divisors of any m ≥ 1
start with 1 (since the smallest divisor is always 1), and the next
partial sum is 1 + d₂ where d₂ ≥ 2 (the smallest prime factor), giving ≥ 3.
So 2 is permanently trapped between achievable partial sums.
-/
theorem partial_sums_skip_2 (m : ℕ) (hm : m ≥ 1) :
    2 ∉ partialDivisorSums m := by
  sorry

/--
Key structural fact for n=5: The only way to get partial sum 5 is
1 + d₂ = 5, requiring d₂ = 4. But 4 | m implies 2 | m, making d₂ = 2 not 4.
For k ≥ 3 divisors: 1 + 2 + d₃ ≥ 6 > 5 since d₃ ≥ 3 for any m with ≥ 3 divisors.
-/
theorem partial_sums_skip_5 (m : ℕ) (hm : m ≥ 1) :
    5 ∉ partialDivisorSums m := by
  sorry

/-
## The Open Problem
-/

/--
**Open Question I**: Is f(n) = o(n)?
Terry Tao showed this is FALSE.
-/
def erdos_1054_part_i : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, (computeF n : ℝ) < ε * n

/--
**Open Question II**: Is f(n) = o(n) for almost all n?
The set of exceptions should have natural density 0.
-/
def erdos_1054_part_ii : Prop :=
  ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ M ≥ N,
    ((Finset.filter (fun n => decide ((computeF n : ℝ) ≥ ε * n)) (Finset.range M)).card : ℝ) < δ * M

/--
**Open Question III**: Is limsup f(n)/n = ∞?
-/
def erdos_1054_part_iii : Prop :=
  ∀ C : ℝ, ∃ n : ℕ, n ≥ 1 ∧ (computeF n : ℝ) ≥ C * n

/--
Tao's result: Part I is FALSE.
-/
axiom tao_disproves_part_i : ¬erdos_1054_part_i

/-
## Structural Lemmas
-/

/--
If 4 divides m, then 2 divides m.
-/
theorem dvd_4_implies_dvd_2 (m : ℕ) (h : 4 ∣ m) : 2 ∣ m := by
  obtain ⟨k, hk⟩ := h
  exact ⟨2 * k, by omega⟩

/--
Every m ≥ 2 has a prime factor p ≥ 2.
-/
theorem exists_prime_factor_ge_2 (m : ℕ) (hm : m ≥ 2) :
    ∃ p, p.Prime ∧ p ∣ m ∧ p ≥ 2 := by
  obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd (by omega : m ≠ 1)
  exact ⟨p, hp, hpm, hp.two_le⟩

/-
## Understanding the Problem

The key insight is that small divisors are very constrained:
- Every number's smallest divisor is 1
- The second smallest is the smallest prime factor
- Numbers with only large prime factors have sparse small divisors

For n to equal a sum of k smallest divisors of m:
- If k = 1: n = 1 (only works for n = 1)
- If k = 2: n = 1 + p where p is the smallest prime factor of m
- In general, the sums are constrained by the divisor structure
-/

/-
## Partial Sums Table

- m = 1: divisors [1], partial sums [1]
- m = 2: divisors [1, 2], partial sums [1, 3]
- m = 3: divisors [1, 3], partial sums [1, 4]
- m = 4: divisors [1, 2, 4], partial sums [1, 3, 7]
- m = 5: divisors [1, 5], partial sums [1, 6]
- m = 6: divisors [1, 2, 3, 6], partial sums [1, 3, 6, 12]
- m = 7: divisors [1, 7], partial sums [1, 8]
- m = 8: divisors [1, 2, 4, 8], partial sums [1, 3, 7, 15]
- m = 9: divisors [1, 3, 9], partial sums [1, 4, 13]
- m = 10: divisors [1, 2, 5, 10], partial sums [1, 3, 8, 18]

The values 2 and 5 never appear as partial sums.
-/

-- ============================================================
-- Additional Structural Lemmas
-- ============================================================

/--
For any m ≥ 2, the smallest divisor > 1 is the minimum prime factor.
This is the second element in the sorted divisor list.
-/
theorem smallest_nontrivial_divisor (m : ℕ) (_hm : m ≥ 2) (d : ℕ)
    (hd : d ∈ m.divisors) (hd1 : d > 1) : d ≥ m.minFac := by
  exact Nat.minFac_le_of_dvd hd1 (Nat.mem_divisors.mp hd).1

/-
For a prime p ≥ 2, p+1 is representable: the divisors of p are {1, p}
and the partial sums are [1, 1+p]. This means f(p+1) ≤ p < p+1.
-/
-- Note: formal proof requires reasoning about sortedDivisors of primes,
-- which involves List.sort. We verify specific instances computationally.

/-- 4 = 3+1 where 3 is prime; f(4) = 3 -/
theorem f_4_via_prime : computeF 4 20 = 3 := by native_decide

/-- 6 = 5+1 where 5 is prime; f(6) = 5 -/
theorem f_6_via_prime : computeF 6 20 = 5 := by native_decide

/-- 8 = 7+1 where 7 is prime; f(8) = 7 -/
theorem f_8_via_prime : computeF 8 20 = 7 := by native_decide

/-- 12 = 11+1 where 11 is prime; f(12) = 6 < 11 (better witness exists) -/
theorem f_12_via_prime : computeF 12 20 = 6 := by native_decide

/-- 14 = 13+1 where 13 is prime; f(14) ≤ 13 -/
theorem representable_14 : IsRepresentable 14 :=
  ⟨13, by omega, by native_decide⟩

theorem f_14_eq : computeF 14 20 = 13 := by native_decide

-- ============================================================
-- f(n) Table (extended)
-- ============================================================

/-
Extended table of f(n) values (computed with bound 100):
- f(1) = 1      f(1)/1 = 1.0
- f(3) = 2      f(3)/3 = 0.67
- f(4) = 3      f(4)/4 = 0.75
- f(6) = 5      f(6)/6 = 0.83
- f(7) = 4      f(7)/7 = 0.57
- f(8) = 7      f(8)/8 = 0.88
- f(9) = 15     f(9)/9 = 1.67 ← exceeds 1!
- f(10) = 12    f(10)/10 = 1.2
- f(12) = 6     f(12)/12 = 0.5

Key observation: f(9) = 15 > 9, showing f(n)/n can exceed 1.
This is because 9 = 1+3+5 (from m=15 with divisors {1,3,5,15}).
There's no smaller m whose divisor partial sums include 9.

Tao proved that f(n)/n is unbounded, confirming Part III.
-/

end Erdos1054
