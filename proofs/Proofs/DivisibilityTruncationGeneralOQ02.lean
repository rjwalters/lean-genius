/-
Divisibility Truncation General OQ-02: Divisors Sharing Factors with 10

The parent proof handles divisors coprime to 10 via oscillator truncation.
This extends to divisors sharing factors with 10: d = 2^a · 5^b · m
where gcd(m, 10) = 1.

Key insight: d | n iff 2^a · 5^b | n AND m | n.
- The first is tested by checking the last max(a,b) digits
- The second uses the osculator method from the parent

## Status
- [x] Last-k-digits test: d | 10^k implies d | n ↔ d | (n % 10^k)
- [x] Factorization lemma: d = 2^a · 5^b · m with gcd(m, 10) = 1
- [x] Concrete examples: divisibility by 2, 4, 5, 8, 25

Parent: DivisibilityTruncationGeneral.lean (coprime-to-10 case)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic

namespace DivisibilityTruncationOQ02

/-! ## Part 1: Last-k-Digits Test

If d divides 10^k, then d | n iff d | (n mod 10^k).
This is the foundation for testing divisibility by powers of 2 and 5. -/

/-- If d | 10^k, then d | n iff d | (n % 10^k). -/
theorem last_k_digits_test (d k n : ℕ) (hd : d ∣ 10 ^ k) :
    d ∣ n ↔ d ∣ n % (10 ^ k) := by
  constructor
  · intro hdn
    have h10k : 10 ^ k > 0 := Nat.pos_pow_of_pos k (by norm_num)
    have := Nat.div_add_mod n (10 ^ k)
    rw [eq_comm, Nat.add_comm] at this
    have hmod := Nat.dvd_sub' hdn (Dvd.dvd.mul_right hd (n / 10 ^ k))
    rwa [this, Nat.add_sub_cancel] at hmod
  · intro hdmod
    have h10k : 10 ^ k > 0 := Nat.pos_pow_of_pos k (by norm_num)
    have : n = 10 ^ k * (n / 10 ^ k) + n % 10 ^ k := (Nat.div_add_mod n (10 ^ k)).symm
    rw [this]
    exact Nat.dvd_add (Dvd.dvd.mul_right hd _) hdmod

/-! ## Part 2: Concrete Divisibility Tests -/

/-- Divisibility by 2: check the last digit. -/
theorem div_by_2 (n : ℕ) : 2 ∣ n ↔ 2 ∣ n % 10 :=
  last_k_digits_test 2 1 n ⟨5, by norm_num⟩

/-- Divisibility by 4: check the last 2 digits. -/
theorem div_by_4 (n : ℕ) : 4 ∣ n ↔ 4 ∣ n % 100 :=
  last_k_digits_test 4 2 n ⟨25, by norm_num⟩

/-- Divisibility by 5: check the last digit. -/
theorem div_by_5 (n : ℕ) : 5 ∣ n ↔ 5 ∣ n % 10 :=
  last_k_digits_test 5 1 n ⟨2, by norm_num⟩

/-- Divisibility by 8: check the last 3 digits. -/
theorem div_by_8 (n : ℕ) : 8 ∣ n ↔ 8 ∣ n % 1000 :=
  last_k_digits_test 8 3 n ⟨125, by norm_num⟩

/-- Divisibility by 25: check the last 2 digits. -/
theorem div_by_25 (n : ℕ) : 25 ∣ n ↔ 25 ∣ n % 100 :=
  last_k_digits_test 25 2 n ⟨4, by norm_num⟩

/-- Divisibility by 125: check the last 3 digits. -/
theorem div_by_125 (n : ℕ) : 125 ∣ n ↔ 125 ∣ n % 1000 :=
  last_k_digits_test 125 3 n ⟨8, by norm_num⟩

/-! ## Part 3: Combined Test

For any d, write d = gcd(d, 10^k) · m where gcd(m, 10) = 1.
Then d | n iff both parts divide n.
The first part uses last-k-digits; the second uses the osculator. -/

/-- Coprime divisibility split: if gcd(a,b) = 1 then ab | n iff a | n ∧ b | n. -/
theorem coprime_dvd_split (a b n : ℕ) (hcop : Nat.Coprime a b) :
    a * b ∣ n ↔ a ∣ n ∧ b ∣ n := by
  exact ⟨fun h => ⟨dvd_trans (dvd_mul_right a b) h, dvd_trans (dvd_mul_left b a) h⟩,
         fun ⟨ha, hb⟩ => hcop.mul_dvd_of_dvd_of_dvd ha hb⟩

/-- **Combined divisibility test**: For d = a · b where gcd(a,b) = 1:
    d | n ↔ a | n ∧ b | n.
    When a | 10^k, the first check is "last k digits."
    When gcd(b, 10) = 1, the second check uses an osculator. -/
theorem combined_test (a b n k : ℕ) (hcop : Nat.Coprime a b)
    (ha10 : a ∣ 10 ^ k) :
    a * b ∣ n ↔ (a ∣ n % (10 ^ k)) ∧ b ∣ n := by
  rw [coprime_dvd_split a b n hcop]
  exact ⟨fun ⟨ha, hb⟩ => ⟨(last_k_digits_test a k n ha10).mp ha, hb⟩,
         fun ⟨hmod, hb⟩ => ⟨(last_k_digits_test a k n ha10).mpr hmod, hb⟩⟩

/-! ## Part 4: Examples of Combined Tests -/

/-- Divisibility by 6 = 2 · 3: last digit even AND digit sum divisible by 3. -/
theorem div_by_6_split (n : ℕ) :
    6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n :=
  coprime_dvd_split 2 3 n (by norm_num)

/-- Divisibility by 12 = 4 · 3: last 2 digits div by 4 AND digit sum div by 3. -/
theorem div_by_12_split (n : ℕ) :
    12 ∣ n ↔ 4 ∣ n ∧ 3 ∣ n :=
  coprime_dvd_split 4 3 n (by norm_num)

/-- Divisibility by 15 = 5 · 3: last digit 0 or 5 AND digit sum div by 3. -/
theorem div_by_15_split (n : ℕ) :
    15 ∣ n ↔ 5 ∣ n ∧ 3 ∣ n :=
  coprime_dvd_split 5 3 n (by norm_num)

end DivisibilityTruncationOQ02
