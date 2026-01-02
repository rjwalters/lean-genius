import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Sum of kth Powers (Faulhaber's Formulas)

## What This Proves
Closed-form formulas for sums of consecutive kth powers. This is Wiedijk's 100 Theorems #77.

The general formula is:
  ∑_{i=1}^{n} i^k = (1/(k+1)) ∑_{j=0}^{k} C(k+1,j) Bⱼ n^(k+1-j)

where Bⱼ are the Bernoulli numbers.

We prove the most famous special cases:
- **Sum of first powers**: ∑i = n(n+1)/2 (Gauss's formula)
- **Sum of squares**: ∑i² = n(n+1)(2n+1)/6
- **Sum of cubes**: ∑i³ = [n(n+1)/2]² = (∑i)²

The last identity is remarkable: the sum of cubes equals the square of the sum!

## Historical Context
Johann Faulhaber (1580-1635) was a German mathematician who discovered closed-form
formulas for sums of powers up to k=17 without knowing the general pattern involving
Bernoulli numbers (which were named after Jacob Bernoulli, who studied them in 1713).

The sum of cubes formula was known to Nicomachus of Gerasa (c. 100 CE) and later
proved by Aryabhata in India (499 CE). The sum of squares formula appears in
Archimedes' work on spirals.

## Approach
- **Foundation (from Mathlib):** We use Mathlib's `Finset.sum_range_id` for sum of
  first powers and prove the higher power cases by induction.
- **Original Contributions:** Direct proofs of the sum of squares and sum of cubes
  formulas, plus the elegant "sum of cubes = square of sum" identity.
- **Proof Techniques Demonstrated:** Induction, algebraic manipulation, divisibility.

## Status
- [x] Complete proof
- [x] Uses Mathlib for basic operations
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Finset.sum_range_id` : Sum of 0..n-1 equals n*(n-1)/2
- `Finset.sum_range_succ` : Splitting off the last term
- `Finset.range` : The set {0, 1, ..., n-1}

## Wiedijk's 100 Theorems: #77
-/

namespace SumOfKthPowers

open Finset BigOperators

/-! ## Sum of First Powers (Gauss's Formula)

The foundation for all power sum formulas. -/

/-- **Sum of first powers (0-indexed)**

    ∑_{i=0}^{n-1} i = n(n-1)/2

    This is Mathlib's convention using range n = {0, 1, ..., n-1}. -/
theorem sum_first_powers (n : ℕ) : ∑ i ∈ range n, i = n * (n - 1) / 2 :=
  Finset.sum_range_id n

/-- **Sum of first powers (classical 1-indexed version)**

    ∑_{i=0}^{n} i = n(n+1)/2

    This is Gauss's formula: 0 + 1 + 2 + ... + n = n(n+1)/2 -/
theorem sum_first_powers_classical (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
  have h := Finset.sum_range_id (n + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [Nat.mul_comm] at h
  exact h

/-! ## Sum of Squares

The formula ∑i² = n(n+1)(2n+1)/6 is one of the most important power sum identities. -/

/-- Helper: 6 divides n(n+1)(2n+1) -/
private lemma six_dvd_sum_squares_formula (n : ℕ) : 6 ∣ n * (n + 1) * (2 * n + 1) := by
  -- n(n+1) is always even (one of them is even)
  have h2 : 2 ∣ n * (n + 1) := by
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · use k * (n + 1)
      calc n * (n + 1) = (k + k) * (n + 1) := by rw [hk]
        _ = 2 * (k * (n + 1)) := by ring
    · use n * (k + 1)
      calc n * (n + 1) = n * (2 * k + 1 + 1) := by rw [hk]
        _ = n * (2 * (k + 1)) := by ring
        _ = 2 * (n * (k + 1)) := by ring
  -- One of n, n+1, 2n+1 is divisible by 3
  have h3 : 3 ∣ n * (n + 1) * (2 * n + 1) := by
    have hmod : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hmod with h | h | h
    · -- n ≡ 0 (mod 3), so 3 | n
      have : 3 ∣ n := Nat.dvd_of_mod_eq_zero h
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right this (n + 1)) (2 * n + 1)
    · -- n ≡ 1 (mod 3), so 2n+1 ≡ 0 (mod 3)
      have hmod21 : (2 * n + 1) % 3 = 0 := by omega
      have h21 : 3 ∣ (2 * n + 1) := Nat.dvd_of_mod_eq_zero hmod21
      exact Dvd.dvd.mul_left h21 _
    · -- n ≡ 2 (mod 3), so n+1 ≡ 0 (mod 3)
      have hmodn1 : (n + 1) % 3 = 0 := by omega
      have hn1 : 3 ∣ (n + 1) := Nat.dvd_of_mod_eq_zero hmodn1
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hn1 n) (2 * n + 1)
  have h2' : 2 ∣ n * (n + 1) * (2 * n + 1) := Dvd.dvd.mul_right h2 _
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2' h3

/-- **Sum of squares times 6**

    6 * ∑_{i=0}^{n} i² = n(n+1)(2n+1)

    Multiplied version avoids division issues. -/
theorem sum_squares_mul_six (n : ℕ) :
    6 * ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    ring

/-- **Sum of squares formula (classical version)**

    ∑_{i=0}^{n} i² = n(n+1)(2n+1)/6

    The most commonly stated form of the sum of squares formula. -/
theorem sum_squares_classical (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
  have h := sum_squares_mul_six n
  have hdvd := six_dvd_sum_squares_formula n
  omega

/-- **Sum of squares formula (0-indexed)**

    ∑_{i=0}^{n-1} i² = n(n-1)(2n-1)/6

    Using range n = {0, 1, ..., n-1}. -/
theorem sum_squares (n : ℕ) : ∑ i ∈ range n, i ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    rw [sum_squares_classical]
    -- m * (m + 1) * (2 * m + 1) / 6 = (m + 1) * m * (2 * (m + 1) - 1) / 6
    -- Note: 2 * (m + 1) - 1 = 2 * m + 2 - 1 = 2 * m + 1
    have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have h2 : (m + 1) * m = m * (m + 1) := by ring
    rw [h1, h2]

/-! ## Sum of Cubes

The remarkable identity ∑i³ = (∑i)² = [n(n+1)/2]² -/

/-- Helper: 2 divides n(n+1) -/
private lemma two_dvd_consecutive (n : ℕ) : 2 ∣ n * (n + 1) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · use k * (n + 1)
    calc n * (n + 1) = (k + k) * (n + 1) := by rw [hk]
      _ = 2 * (k * (n + 1)) := by ring
  · use n * (k + 1)
    calc n * (n + 1) = n * (2 * k + 1 + 1) := by rw [hk]
      _ = n * (2 * (k + 1)) := by ring
      _ = 2 * (n * (k + 1)) := by ring

/-- **Sum of cubes times 4**

    4 * ∑_{i=0}^{n} i³ = [n(n+1)]²

    Multiplied version avoids division issues. -/
theorem sum_cubes_mul_four (n : ℕ) :
    4 * ∑ i ∈ range (n + 1), i ^ 3 = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add, ih]
    ring

/-- **Sum of cubes formula (classical version)**

    ∑_{i=0}^{n} i³ = [n(n+1)/2]²

    The most commonly stated form. -/
theorem sum_cubes_classical (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  have h := sum_cubes_mul_four n
  have hdvd := two_dvd_consecutive n
  obtain ⟨k, hk⟩ := hdvd
  have hk' : n * (n + 1) / 2 = k := by
    calc n * (n + 1) / 2 = (2 * k) / 2 := by rw [hk]
      _ = k := Nat.mul_div_cancel_left k (by norm_num : 0 < 2)
  have hsq : (n * (n + 1)) ^ 2 = (2 * k) ^ 2 := by rw [hk]
  have hsq2 : (2 * k) ^ 2 = 4 * k ^ 2 := by ring
  calc ∑ i ∈ range (n + 1), i ^ 3
      = (n * (n + 1)) ^ 2 / 4 := by omega
    _ = (2 * k) ^ 2 / 4 := by rw [hsq]
    _ = 4 * k ^ 2 / 4 := by rw [hsq2]
    _ = k ^ 2 := Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)
    _ = (n * (n + 1) / 2) ^ 2 := by rw [hk']

/-- **Sum of cubes formula (0-indexed)**

    ∑_{i=0}^{n-1} i³ = [n(n-1)/2]²

    Using range n = {0, 1, ..., n-1}. -/
theorem sum_cubes (n : ℕ) : ∑ i ∈ range n, i ^ 3 = (n * (n - 1) / 2) ^ 2 := by
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    rw [sum_cubes_classical]
    have h2 : m * (m + 1) = (m + 1) * m := by ring
    rw [h2]

/-! ## The Remarkable Identity: Sum of Cubes = Square of Sum

This is one of the most elegant identities in mathematics: the sum of the first n
cubes equals the square of the sum of the first n natural numbers. -/

/-- **Sum of cubes equals square of sum**

    ∑_{i=0}^{n} i³ = (∑_{i=0}^{n} i)²

    This remarkable identity connects two seemingly unrelated sums. -/
theorem sum_cubes_eq_sum_squared (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 3 = (∑ i ∈ range (n + 1), i) ^ 2 := by
  rw [sum_cubes_classical, sum_first_powers_classical]

/-- **Alternative statement with explicit formula**

    (1³ + 2³ + ... + n³) = (1 + 2 + ... + n)² -/
theorem nicomachus_theorem (n : ℕ) :
    (∑ i ∈ range (n + 1), i ^ 3) = (∑ i ∈ range (n + 1), i) ^ 2 :=
  sum_cubes_eq_sum_squared n

/-! ## Verification Examples -/

/-- Sum of squares from 0 to 10: 0² + 1² + ... + 10² = 385 -/
theorem sum_squares_10 : ∑ i ∈ range 11, i ^ 2 = 385 := by native_decide

/-- Sum of cubes from 0 to 10: 0³ + 1³ + ... + 10³ = 3025 = 55² -/
theorem sum_cubes_10 : ∑ i ∈ range 11, i ^ 3 = 3025 := by native_decide

/-- Verification: 55² = 3025 (confirming Nicomachus) -/
theorem sum_10_squared : (∑ i ∈ range 11, i) ^ 2 = 3025 := by native_decide

/-- Sum of first 100 squares -/
theorem sum_squares_100 : ∑ i ∈ range 101, i ^ 2 = 338350 := by native_decide

/-- Sum of first 100 cubes = 25502500 = 5050² -/
theorem sum_cubes_100 : ∑ i ∈ range 101, i ^ 3 = 25502500 := by native_decide

/-! ## Higher Powers (Without Closed Forms)

For k ≥ 4, closed forms exist but involve Bernoulli numbers and become complex.
We demonstrate the sums exist and can be computed. -/

/-- Sum of fourth powers from 0 to n can be computed -/
theorem sum_fourth_powers_5 : ∑ i ∈ range 6, i ^ 4 = 979 := by native_decide

/-- Sum of fifth powers from 0 to n can be computed -/
theorem sum_fifth_powers_5 : ∑ i ∈ range 6, i ^ 5 = 4425 := by native_decide

/-! ## Key Theorems Summary -/

#check sum_first_powers
#check sum_first_powers_classical
#check sum_squares
#check sum_squares_classical
#check sum_cubes
#check sum_cubes_classical
#check sum_cubes_eq_sum_squared
#check nicomachus_theorem

end SumOfKthPowers
