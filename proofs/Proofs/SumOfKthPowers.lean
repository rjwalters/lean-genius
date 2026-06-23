import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Tactic

/-
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

/- ## Sum of First Powers (Gauss's Formula)

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

/- ## Sum of Squares

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
    simp only [Nat.add_sub_cancel]
    rw [sum_squares_classical]
    -- m * (m + 1) * (2 * m + 1) / 6 = (m + 1) * m * (2 * (m + 1) - 1) / 6
    -- Note: 2 * (m + 1) - 1 = 2 * m + 2 - 1 = 2 * m + 1
    have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have h2 : (m + 1) * m = m * (m + 1) := by ring
    rw [h1, h2]

/- ## Sum of Cubes

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
    simp only [Nat.add_sub_cancel]
    rw [sum_cubes_classical]
    have h2 : m * (m + 1) = (m + 1) * m := by ring
    rw [h2]

/- ## The Remarkable Identity: Sum of Cubes = Square of Sum

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

/- ## Sum of Fourth Powers

The formula ∑i⁴ = n(n+1)(2n+1)(3n²+3n-1)/30

To avoid natural number subtraction issues, we work with the equivalent form:
  30 * ∑i⁴ + n(n+1)(2n+1) = n(n+1)(2n+1) * (3n² + 3n)
which rearranges to:
  30 * ∑i⁴ = n(n+1)(2n+1)(3n² + 3n) - n(n+1)(2n+1)
           = n(n+1)(2n+1)(3n² + 3n - 1)
-/

/-- **Sum of fourth powers times 30 (rearranged)**

    30 * ∑_{i=0}^{n} i⁴ + n(n+1)(2n+1) = 3n²(n+1)²(2n+1)

    Rearranged to avoid natural number subtraction. This is equivalent to
    30 * ∑i⁴ = n(n+1)(2n+1)(3n²+3n-1). -/
theorem sum_fourth_powers_mul_thirty (n : ℕ) :
    30 * ∑ i ∈ range (n + 1), i ^ 4 + n * (n + 1) * (2 * n + 1) =
    3 * n ^ 2 * (n + 1) ^ 2 * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add]
    nlinarith [ih]

/-- Helper: 30 divides 3n²(n+1)²(2n+1) - n(n+1)(2n+1). -/
private lemma thirty_dvd_fourth_sum (n : ℕ) :
    30 ∣ (3 * n ^ 2 * (n + 1) ^ 2 * (2 * n + 1) - n * (n + 1) * (2 * n + 1)) := by
  have h := sum_fourth_powers_mul_thirty n
  use ∑ i ∈ range (n + 1), i ^ 4
  omega

/-- **Sum of fourth powers formula (classical version)**

    ∑_{i=0}^{n} i⁴ = (3n²(n+1)²(2n+1) - n(n+1)(2n+1)) / 30

    Equivalently: n(n+1)(2n+1)(3n²+3n-1)/30. -/
theorem sum_fourth_powers_classical (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 4 =
    (3 * n ^ 2 * (n + 1) ^ 2 * (2 * n + 1) - n * (n + 1) * (2 * n + 1)) / 30 := by
  have h := sum_fourth_powers_mul_thirty n
  have hdvd := thirty_dvd_fourth_sum n
  omega

/- ## Sum of Fifth Powers

The formula ∑i⁵ = n²(n+1)²(2n²+2n-1)/12

To avoid natural number subtraction, we use:
  12 * ∑i⁵ + n²(n+1)² = n²(n+1)² * (2n² + 2n)
which rearranges to:
  12 * ∑i⁵ = n²(n+1)²(2n² + 2n - 1)
-/

/-- **Sum of fifth powers times 12 (rearranged)**

    12 * ∑_{i=0}^{n} i⁵ + n²(n+1)² = 2n³(n+1)³

    Rearranged to avoid natural number subtraction. This is equivalent to
    12 * ∑i⁵ = n²(n+1)²(2n²+2n-1). -/
theorem sum_fifth_powers_mul_twelve (n : ℕ) :
    12 * ∑ i ∈ range (n + 1), i ^ 5 + n ^ 2 * (n + 1) ^ 2 =
    2 * n ^ 3 * (n + 1) ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add]
    nlinarith [ih]

/-- Helper: 12 divides 2n³(n+1)³ - n²(n+1)². -/
private lemma twelve_dvd_fifth_sum (n : ℕ) :
    12 ∣ (2 * n ^ 3 * (n + 1) ^ 3 - n ^ 2 * (n + 1) ^ 2) := by
  have h := sum_fifth_powers_mul_twelve n
  use ∑ i ∈ range (n + 1), i ^ 5
  omega

/-- **Sum of fifth powers formula (classical version)**

    ∑_{i=0}^{n} i⁵ = (2n³(n+1)³ - n²(n+1)²) / 12

    Equivalently: n²(n+1)²(2n²+2n-1)/12. -/
theorem sum_fifth_powers_classical (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 5 =
    (2 * n ^ 3 * (n + 1) ^ 3 - n ^ 2 * (n + 1) ^ 2) / 12 := by
  have h := sum_fifth_powers_mul_twelve n
  have hdvd := twelve_dvd_fifth_sum n
  omega

/- ## Sum of Sixth Powers

The formula ∑i⁶ = n(n+1)(2n+1)(3n⁴+6n³-3n+1)/42

To avoid natural number subtraction, we use:
  42 * ∑i⁶ + 3n²(n+1)(2n+1) = n(n+1)(2n+1)(3n⁴ + 6n³ + 1)
-/

/-- **Sum of sixth powers times 42 (rearranged)**

    42 * ∑_{i=0}^{n} i⁶ + 3n²(n+1)(2n+1) = n(n+1)(2n+1)(3n⁴ + 6n³ + 1)

    Rearranged to avoid natural number subtraction. This is equivalent to
    42 * ∑i⁶ = n(n+1)(2n+1)(3n⁴ + 6n³ - 3n + 1). -/
theorem sum_sixth_powers_mul_fortytwo (n : ℕ) :
    42 * ∑ i ∈ range (n + 1), i ^ 6 + 3 * n ^ 2 * (n + 1) * (2 * n + 1) =
    n * (n + 1) * (2 * n + 1) * (3 * n ^ 4 + 6 * n ^ 3 + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add]
    nlinarith [ih]

/-- Helper: 42 divides the RHS minus LHS constant term. -/
private lemma fortytwo_dvd_sixth_sum (n : ℕ) :
    42 ∣ (n * (n + 1) * (2 * n + 1) * (3 * n ^ 4 + 6 * n ^ 3 + 1)
         - 3 * n ^ 2 * (n + 1) * (2 * n + 1)) := by
  have h := sum_sixth_powers_mul_fortytwo n
  use ∑ i ∈ range (n + 1), i ^ 6
  omega

/-- **Sum of sixth powers formula (classical version)**

    ∑_{i=0}^{n} i⁶ = (n(n+1)(2n+1)(3n⁴+6n³+1) - 3n²(n+1)(2n+1)) / 42 -/
theorem sum_sixth_powers_classical (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 6 =
    (n * (n + 1) * (2 * n + 1) * (3 * n ^ 4 + 6 * n ^ 3 + 1)
     - 3 * n ^ 2 * (n + 1) * (2 * n + 1)) / 42 := by
  have h := sum_sixth_powers_mul_fortytwo n
  have hdvd := fortytwo_dvd_sixth_sum n
  omega

/- ## Sum of Seventh Powers

The formula ∑i⁷ = n²(n+1)²(3n⁴+6n³-n²-4n+2)/24

To avoid natural number subtraction, we use:
  24 * ∑i⁷ + n²(n+1)²(n² + 4n) = n²(n+1)² * (3n⁴ + 6n³ + 2)
which rearranges to:
  24 * ∑i⁷ = n²(n+1)²(3n⁴ + 6n³ - n² - 4n + 2)
-/

/-- **Sum of seventh powers times 24 (rearranged)**

    24 * ∑_{i=0}^{n} i⁷ + n²(n+1)²(n² + 4n) = n²(n+1)²(3n⁴ + 6n³ + 2)

    Rearranged to avoid natural number subtraction. This is equivalent to
    24 * ∑i⁷ = n²(n+1)²(3n⁴ + 6n³ - n² - 4n + 2). -/
theorem sum_seventh_powers_mul_twentyfour (n : ℕ) :
    24 * ∑ i ∈ range (n + 1), i ^ 7 + n ^ 2 * (n + 1) ^ 2 * (n ^ 2 + 4 * n) =
    n ^ 2 * (n + 1) ^ 2 * (3 * n ^ 4 + 6 * n ^ 3 + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, Nat.mul_add]
    nlinarith [ih]

/-- Helper: 24 divides the RHS minus LHS constant term. -/
private lemma twentyfour_dvd_seventh_sum (n : ℕ) :
    24 ∣ (n ^ 2 * (n + 1) ^ 2 * (3 * n ^ 4 + 6 * n ^ 3 + 2)
         - n ^ 2 * (n + 1) ^ 2 * (n ^ 2 + 4 * n)) := by
  have h := sum_seventh_powers_mul_twentyfour n
  use ∑ i ∈ range (n + 1), i ^ 7
  omega

/-- **Sum of seventh powers formula (classical version)**

    ∑_{i=0}^{n} i⁷ = (n²(n+1)²(3n⁴+6n³+2) - n²(n+1)²(n²+4n)) / 24 -/
theorem sum_seventh_powers_classical (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 7 =
    (n ^ 2 * (n + 1) ^ 2 * (3 * n ^ 4 + 6 * n ^ 3 + 2)
     - n ^ 2 * (n + 1) ^ 2 * (n ^ 2 + 4 * n)) / 24 := by
  have h := sum_seventh_powers_mul_twentyfour n
  have hdvd := twentyfour_dvd_seventh_sum n
  omega

/- ## Verification Examples -/

/-- Sum of sixth powers from 0 to 10 -/
theorem sum_sixth_powers_10 : ∑ i ∈ range 11, i ^ 6 = 1978405 := by native_decide

/-- Sum of seventh powers from 0 to 5: verified -/
theorem sum_seventh_powers_5 : ∑ i ∈ range 6, i ^ 7 = 96825 := by native_decide

/-- Sum of seventh powers from 0 to 10 -/
theorem sum_seventh_powers_10 : ∑ i ∈ range 11, i ^ 7 = 18080425 := by native_decide

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

/-- Sum of fourth powers from 0 to 5: verified -/
theorem sum_fourth_powers_5 : ∑ i ∈ range 6, i ^ 4 = 979 := by native_decide

/-- Sum of fourth powers from 0 to 10 -/
theorem sum_fourth_powers_10 : ∑ i ∈ range 11, i ^ 4 = 25333 := by native_decide

/-- Sum of fifth powers from 0 to 5: verified -/
theorem sum_fifth_powers_5 : ∑ i ∈ range 6, i ^ 5 = 4425 := by native_decide

/-- Sum of fifth powers from 0 to 10 -/
theorem sum_fifth_powers_10 : ∑ i ∈ range 11, i ^ 5 = 220825 := by native_decide

/-- Verification: sum of 4th powers formula for n=10 -/
theorem sum_fourth_formula_check_10 :
    (3 * 100 * 121 * 21 - 10 * 11 * 21) / 30 = 25333 := by native_decide

/-- Verification: sum of 5th powers formula for n=10 -/
theorem sum_fifth_formula_check_10 :
    (2 * 1000 * 1331 - 100 * 121) / 12 = 220825 := by native_decide

/- ## Structural Properties -/

/-- Sum of k-th powers is zero when the range is empty. -/
theorem sum_pow_zero_range (k : ℕ) : ∑ i ∈ range 0, i ^ k = 0 := by simp

/-- Sum of k-th powers is monotone in the range: adding one more term increases the sum. -/
theorem sum_pow_le_succ (n k : ℕ) :
    ∑ i ∈ range n, i ^ k ≤ ∑ i ∈ range (n + 1), i ^ k := by
  rw [sum_range_succ]
  omega

/-- Each summand i^k ≤ n^k for i < n+1, giving an upper bound. -/
theorem sum_pow_le_mul (n k : ℕ) :
    ∑ i ∈ range (n + 1), i ^ k ≤ (n + 1) * n ^ k := by
  calc ∑ i ∈ range (n + 1), i ^ k
      ≤ ∑ _i ∈ range (n + 1), n ^ k := by
        apply Finset.sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_left (by simp [Finset.mem_range] at hi; omega) k
    _ = (n + 1) * n ^ k := by simp [Finset.sum_const, Finset.card_range]

/-- The sum of k-th powers is at least n^k (from the last term). -/
theorem sum_pow_ge_last (n k : ℕ) :
    ∑ i ∈ range (n + 1), i ^ k ≥ n ^ k := by
  rw [sum_range_succ]
  omega

/-- The sum of 0th powers from 0 to n is n+1 (counting). -/
theorem sum_zeroth_powers (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 0 = n + 1 := by
  simp

/-- Sum of cubes of even numbers: ∑_{i=0}^{n} (2i)³ = 8 · ∑_{i=0}^{n} i³. -/
theorem sum_even_cubes (n : ℕ) :
    ∑ i ∈ range (n + 1), (2 * i) ^ 3 = 8 * ∑ i ∈ range (n + 1), i ^ 3 := by
  simp only [mul_pow]
  rw [← Finset.mul_sum]
  ring_nf

/-- Telescoping: the difference of consecutive power sums gives the last term. -/
theorem sum_pow_succ_sub (n k : ℕ) :
    ∑ i ∈ range (n + 1), i ^ k - ∑ i ∈ range n, i ^ k = n ^ k := by
  rw [sum_range_succ]
  omega

/- ## Connection to Bernoulli Numbers: The General Faulhaber Formula

Mathlib provides the general Faulhaber formula via `Finset.sum_range_pow`, which expresses
∑_{i=0}^{n-1} i^p as a polynomial in n with Bernoulli number coefficients:

  ∑_{i=0}^{n-1} i^p = ∑_{i=0}^{p} B_i · C(p+1,i) · n^(p+1-i) / (p+1)

This subsumes all our specific formulas (k=1 through k=7) as special cases. -/

section BernoulliConnection

/-- The general Faulhaber formula over ℚ.
    This is a restatement of Mathlib's `Finset.sum_range_pow` to make the connection explicit.
    For any p, the sum of p-th powers is a degree-(p+1) polynomial in n with
    Bernoulli number coefficients. -/
theorem faulhaber_formula (n p : ℕ) :
    (∑ i ∈ range n, (i : ℚ) ^ p) =
    ∑ i ∈ range (p + 1), bernoulli i * ↑((p + 1).choose i) * (n : ℚ) ^ (p + 1 - i) / (↑p + 1) :=
  Finset.sum_range_pow n p

/-- The general formula via Bernoulli polynomial evaluation:
    (p+1) · ∑_{i=0}^{n-1} i^p = B_{p+1}(n) - B_{p+1}
    where B_k is the k-th Bernoulli polynomial. -/
theorem faulhaber_bernoulli_poly (n p : ℕ) :
    ((↑p + 1 : ℚ) * ∑ i ∈ range n, (i : ℚ) ^ p) =
    (Polynomial.bernoulli p.succ).eval (n : ℚ) - (Polynomial.bernoulli p.succ).eval 0 :=
  Finset.sum_range_pow_eq_bernoulli_sub n p

/-- Bernoulli polynomial evaluated at 0 gives the Bernoulli number. -/
theorem bernoulli_poly_eval_zero (n : ℕ) :
    (Polynomial.bernoulli n).eval (0 : ℚ) = bernoulli n :=
  Polynomial.bernoulli_eval_zero n

/-- **Verification: Faulhaber for p=1 gives Gauss's formula**

    ∑_{i=0}^{n-1} i = n(n-1)/2 over ℚ. -/
theorem faulhaber_p1 (n : ℕ) :
    (∑ i ∈ range n, (i : ℚ) ^ 1) = (n : ℚ) * ((n : ℚ) - 1) / 2 := by
  have h := faulhaber_formula n 1
  simp [bernoulli, Polynomial.bernoulli] at h ⊢
  linarith

/-- **The Faulhaber formula via Bernoulli polynomial evaluation (simplified)**

    ∑_{i=0}^{n-1} i^p = (B_{p+1}(n) - B_{p+1}(0)) / (p+1)

    This shows power sums are computed by evaluating Bernoulli polynomials. -/
theorem faulhaber_via_eval (n p : ℕ) :
    (∑ i ∈ range n, (i : ℚ) ^ p) =
    ((Polynomial.bernoulli p.succ).eval (n : ℚ) - (Polynomial.bernoulli p.succ).eval 0) /
    (↑p + 1) := by
  have hp : (↑p + 1 : ℚ) ≠ 0 := by positivity
  have h := faulhaber_bernoulli_poly n p
  field_simp at h ⊢
  linarith

/-- **Odd Bernoulli numbers vanish (except B₁)**

    B_{2k+1} = 0 for k ≥ 1. This is why even power sum formulas
    only involve even-index Bernoulli numbers. -/
theorem bernoulli_odd_eq_zero {n : ℕ} (h1 : n ≠ 1) (h2 : ¬Even n) :
    bernoulli n = 0 :=
  Nat.bernoulli_odd_eq_zero h1 h2

/-- **B₀ = 1** -/
theorem bernoulli_zero_val : bernoulli 0 = 1 :=
  bernoulli_zero

/-- **B₁ = -1/2** (in Mathlib's convention) -/
theorem bernoulli_one_val : bernoulli 1 = -1/2 :=
  bernoulli_one

/-- **Connection between ℕ and ℚ formulas for sum of squares**

    The ℕ formula n(n+1)(2n+1)/6 equals the Faulhaber formula evaluated over ℚ. -/
theorem sum_squares_bernoulli_agreement (n : ℕ) :
    (↑(∑ i ∈ range (n + 1), i ^ 2) : ℚ) =
    ∑ i ∈ range 3, bernoulli i * ↑(3.choose i) * (↑(n + 1) : ℚ) ^ (3 - i) / 3 := by
  have h := faulhaber_formula (n + 1) 2
  exact_mod_cast h

/-- **Connection between ℕ and ℚ formulas for sum of cubes**

    The ℕ formula [n(n+1)/2]² equals the Faulhaber formula evaluated over ℚ. -/
theorem sum_cubes_bernoulli_agreement (n : ℕ) :
    (↑(∑ i ∈ range (n + 1), i ^ 3) : ℚ) =
    ∑ i ∈ range 4, bernoulli i * ↑(4.choose i) * (↑(n + 1) : ℚ) ^ (4 - i) / 4 := by
  have h := faulhaber_formula (n + 1) 3
  exact_mod_cast h

end BernoulliConnection

end SumOfKthPowers
